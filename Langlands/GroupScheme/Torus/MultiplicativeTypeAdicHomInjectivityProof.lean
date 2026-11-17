import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicHomInjectivityStatement
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Adic determination of homomorphisms from isotrivial multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace AdicHomInjectivity

private theorem hausdorff_groupAlgebra {A B Λ : Type u} [CommRing A] [CommRing B]
    [AddCommGroup Λ] [Algebra A B] (I : Ideal A) [IsHausdorff I B] :
    IsHausdorff I (AddMonoidAlgebra B Λ) := by
  constructor
  intro x hx
  apply AddMonoidAlgebra.ext
  ext l
  apply IsHausdorff.haus (I := I) (M := B) inferInstance (x.coeff l)
  intro n
  apply SModEq.zero.mpr
  exact Submodule.smul_top_le_comap_smul_top (I ^ n)
    ((Finsupp.lapply l).comp (AddMonoidAlgebra.coeffLinearEquiv A).toLinearMap)
    (SModEq.zero.mp (hx n))

private theorem hom_eq_of_quotient_precomp {R : Type u} [CommRing R]
    (I : Ideal R) [IsHausdorff I R] {Y : Scheme.{u}} [IsAffine Y]
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ g) :
    f = g := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom).mp
  have he (n : ℕ) :
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) =
        g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.comp_appTop_assoc, h n,
      Scheme.Hom.comp_appTop_assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  have hf := IsHausdorff.StrictMono.funext' I (a := fun n : ℕ => n + 1)
    (fun _ _ hab => Nat.add_lt_add_right hab 1)
    (f := (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom)
    (g := (g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom)
    (fun n r => congrArg (fun k => k.hom r) (he n))
  exact congrFun hf x

@[reassoc] private theorem baseChange_map_fst {S S' : Scheme.{u}} (s : S' ⟶ S)
    {H G : GroupScheme S} (f : H ⟶ G) :
    ((GroupScheme.baseChange s).map f).hom.hom.left ≫ pullback.fst G.X.hom s =
      pullback.fst H.X.hom s ≫ f.hom.hom.left := by
  exact pullback.lift_fst _ _ _

private theorem eq_precomp_of_reductions {A T : Type u} [CommRing A] [CommRing T]
    [Algebra A T] (I : Ideal A) [IsHausdorff I T]
    {H G : GroupScheme (Spec (CommRingCat.of A))} [IsAffine G.X.left]
    (f g : H ⟶ G)
    (h : ∀ n : ℕ,
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).map f =
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).map g)
    (q : Spec (CommRingCat.of T) ⟶ H.X.left)
    (hq : q ≫ H.X.hom = Spec.algebraMap A T) :
    q ≫ f.hom.hom.left = q ≫ g.hom.hom.left := by
  let J := I.map (algebraMap A T)
  let : IsHausdorff J T := IsHausdorff.map_algebraMap_iff.mpr inferInstance
  apply hom_eq_of_quotient_precomp J
  intro n
  let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))
  let s := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))
  let φ : A ⧸ I ^ (n + 1) →+* T ⧸ J ^ (n + 1) :=
    Ideal.quotientMap (J ^ (n + 1)) (algebraMap A T)
      (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
  let t := Spec.map (CommRingCat.ofHom φ)
  have hs : r ≫ Spec.algebraMap A T = t ≫ s := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let l : Spec (CommRingCat.of (T ⧸ J ^ (n + 1))) ⟶ pullback H.X.hom s :=
    pullback.lift (r ≫ q) t (by rw [Category.assoc, hq]; exact hs)
  have he := congrArg (fun k => l ≫ k.hom.hom.left ≫ pullback.fst G.X.hom s) (h n)
  change l ≫ ((GroupScheme.baseChange s).map f).hom.hom.left ≫ pullback.fst G.X.hom s =
    l ≫ ((GroupScheme.baseChange s).map g).hom.hom.left ≫ pullback.fst G.X.hom s at he
  rw [baseChange_map_fst s f, baseChange_map_fst s g] at he
  simpa only [← Category.assoc, l, pullback.lift_fst] using he

end AdicHomInjectivity

open AdicHomInjectivity RelativeMultiplicativeType

/-- Adic reductions determine homomorphisms from an isotrivial group of multiplicative type
to an affine group (SGA 3, Exposé IX, Théorème 7.1, injectivity). -/
theorem multiplicativeTypeAdicHomInjectivity :
    MultiplicativeTypeAdicHomInjectivityStatement.{u} := by
  intro A _ _ I _ H G _ hsplit f g h
  obtain ⟨S', p, hpfin, hpet, hpsur, hH⟩ := hsplit
  let : IsFinite p := hpfin
  let : Etale p := hpet
  let : Surjective p := hpsur
  let : IsAffine S' := isAffine_of_isAffineHom p
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let B : CommRingCat.{u} := Γ(S', ⊤)
  let b : Spec B ⟶ Spec (CommRingCat.of A) := S'.isoSpec.inv ≫ p
  let : Algebra A B := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.algebraMap A B = b := Spec.map_preimage b
  let : IsFinite b := by dsimp [b]; infer_instance
  let : Flat b := by dsimp [b]; infer_instance
  let : Surjective b := by dsimp [b]; infer_instance
  let : Module.Finite A B := by
    apply (IsFinite.SpecMap_iff (Spec.preimage b)).mp
    rw [Spec.map_preimage]
    infer_instance
  let : IsHausdorff I B :=
    IsHausdorff.of_le_jacobson I B (IsAdicComplete.le_jacobson_bot I)
  have hHb : IsDiagonalizable ((GroupScheme.baseChange b).obj H) :=
    IsDiagonalizable.of_iso
      (Descent.pullbackComparison p S'.isoSpec.inv b rfl H).symm
      (hH.baseChange S'.isoSpec.inv)
  obtain ⟨N, _, _, ⟨e⟩⟩ := hHb
  let d : (Diagonalizable.groupScheme B N).toGrp ≅
      (GroupScheme.baseChange b).obj H :=
    (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec B)) N).symm ≪≫ e.symm
  let T := AddMonoidAlgebra B N
  let : IsHausdorff I T := hausdorff_groupAlgebra I
  let q : Spec (CommRingCat.of T) ⟶ H.X.left :=
    d.hom.hom.hom.left ≫ pullback.fst H.X.hom b
  have hq : q ≫ H.X.hom = Spec.algebraMap A T := by
    have hdw : d.hom.hom.hom.left ≫ pullback.snd H.X.hom b =
        Spec.algebraMap B T := Over.w d.hom.hom.hom
    dsimp only [q]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hdw]
    change Spec.algebraMap B T ≫ b = Spec.algebraMap A T
    rw [← hb, ← Spec.map_comp]
    congr 1
  have he := eq_precomp_of_reductions I f g h q hq
  let : IsIso d.hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec B)).map d.hom.hom.hom))
  have he' : pullback.fst H.X.hom b ≫ f.hom.hom.left =
      pullback.fst H.X.hom b ≫ g.hom.hom.left := by
    apply (cancel_epi d.hom.hom.hom.left).mp
    simpa only [q, Category.assoc] using he
  let : Epi (pullback.fst H.X.hom b) := Flat.epi_of_flat_of_surjective _
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_epi (pullback.fst H.X.hom b)).mp he'

end Langlands.GroupScheme
