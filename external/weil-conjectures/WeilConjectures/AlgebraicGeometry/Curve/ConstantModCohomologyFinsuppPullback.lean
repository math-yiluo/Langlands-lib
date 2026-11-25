/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit

/-! # Functorial direct-sum coordinates for constant coefficients modulo a prime -/

@[expose] public section

universe u
open CategoryTheory

-- A coproduct is the filtered colimit of its finite subcoproducts.
set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits in
private noncomputable def coproduct_preserved_of_finite_subcoproducts
    {C D : Type*} [Category C] [Category D] [HasFiniteCoproducts C]
    (F : C ⥤ D) [PreservesFiniteCoproducts F] {I : Type*} (a : I → C)
    [HasCoproduct a]
    (hc : IsColimit (F.mapCocone
      (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone a))) :
    IsColimit (Cofan.mk (F.obj (∐ a)) (fun i ↦ F.map (Sigma.ι a i))) := by
  classical
  let fin (s : Finset (Discrete I)) :=
    isColimitOfHasCoproductOfPreservesColimit F (fun i : s ↦ a i.val.as)
  let lift (s : Cofan (fun i ↦ F.obj (a i))) :
      Cocone (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor a) ⋙ F) :=
    { pt := s.pt
      ι :=
        { app := fun t ↦ (fin t).desc (Cofan.mk s.pt (fun i ↦ s.ι.app i.val))
          naturality := by
            intro t t' f
            apply (fin t).hom_ext
            intro i
            change F.map (Sigma.ι _ i.as) ≫ F.map _ ≫ _ =
              F.map (Sigma.ι _ i.as) ≫ _ ≫ 𝟙 _
            rw [Category.comp_id, ← F.map_comp_assoc]
            simp only [CoproductsFromFiniteFiltered.liftToFinsetObj_map, Sigma.ι_comp_desc]
            have h₁ := (fin t').fac (Cofan.mk s.pt (fun i ↦ s.ι.app i.val))
              ⟨⟨i.as.val, f.down.down i.as.property⟩⟩
            have h₂ := (fin t).fac (Cofan.mk s.pt (fun i ↦ s.ι.app i.val)) i
            exact h₁.trans h₂.symm } }
  refine
    { desc := fun s ↦ hc.desc (lift s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    let t : Finset (Discrete I) := {i}
    let j : t := ⟨i, by simp [t]⟩
    have h : Sigma.ι (fun x : t ↦ a x.val.as) j ≫
        (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone a).ι.app t =
        Sigma.ι a i.as := by simp [j]
    change F.map (Sigma.ι a i.as) ≫ hc.desc (lift s) = s.ι.app i
    rw [← h, F.map_comp, Category.assoc]
    have hh := hc.fac (lift s) t
    change F.map (Sigma.desc (fun x : t ↦ Sigma.ι a x.val.as)) ≫
      hc.desc (lift s) = (fin t).desc (Cofan.mk s.pt (fun i ↦ s.ι.app i.val)) at hh
    simp only [CoproductsFromFiniteFiltered.finiteSubcoproductsCocone_ι_app]
    rw [hh]
    simpa [j] using (fin t).fac (Cofan.mk s.pt (fun i ↦ s.ι.app i.val)) ⟨j⟩
  · intro s m hm
    apply hc.hom_ext
    intro t
    apply (fin t).hom_ext
    intro i
    change F.map (Sigma.ι _ i.as) ≫ F.map _ ≫ m =
      F.map (Sigma.ι _ i.as) ≫ F.map _ ≫ hc.desc (lift s)
    rw [← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [CoproductsFromFiniteFiltered.finiteSubcoproductsCocone_ι_app,
      Sigma.ι_comp_desc]
    have hh := hc.fac (lift s) t
    have hh' := congrArg (fun k ↦ F.map (Sigma.ι (fun x : t ↦ a x.val.as) i.as) ≫ k) hh
    have hfac := (fin t).fac (Cofan.mk s.pt (fun i ↦ s.ι.app i.val)) i
    have hright := hh'.trans hfac
    change F.map (Sigma.ι (fun x : t ↦ a x.val.as) i.as) ≫
      F.map (Sigma.desc (fun x : t ↦ Sigma.ι a x.val.as)) ≫
        hc.desc (lift s) = s.ι.app i.as.val at hright
    simp only [← F.map_comp_assoc, Sigma.ι_comp_desc] at hright
    exact (hm i.as.val).trans hright.symm

open CategoryTheory.Limits in
private noncomputable def finsupp_cofan (I : Type (u + 1)) (A : AddCommGrpCat.{u + 1}) :
    Cofan (fun _ : I ↦ A) :=
  Cofan.mk (AddCommGrpCat.of (I →₀ A))
    (fun i ↦ AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := A) i))

open CategoryTheory.Limits in
private noncomputable def finsupp_cofan_isColimit
    (I : Type (u + 1)) (A : AddCommGrpCat.{u + 1}) :
    IsColimit (finsupp_cofan I A) where
  desc s := AddCommGrpCat.ofHom (Finsupp.liftAddHom (fun i ↦ (s.ι.app ⟨i⟩).hom))
  fac s i := by
    ext x
    exact Finsupp.liftAddHom_apply_single _ i.as x
  uniq s f h := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro i x
    simpa [finsupp_cofan, Finsupp.liftAddHom_apply_single] using
      ConcreteCategory.congr_hom (h ⟨i⟩) x

-- Uniqueness of coproduct maps turns naturality on summands into naturality on Finsupp.
open CategoryTheory.Limits in
private theorem natural_finsupp_coordinates
    {C : Type*} [Category C] (I : Type (u + 1)) {A H : C} (j : I → (A ⟶ H))
    (F Q : C ⥤ AddCommGrpCat.{u + 1}) (τ : F ⟶ Q)
    (hF : IsColimit (Cofan.mk (F.obj H) (fun i : I ↦ F.map (j i))))
    (hQ : IsColimit (Cofan.mk (Q.obj H) (fun i : I ↦ Q.map (j i)))) :
    ∃ (a : F.obj H ≃+ (I →₀ ↥(F.obj A))) (b : Q.obj H ≃+ (I →₀ ↥(Q.obj A))),
      ∀ x i, b (τ.app H x) i = τ.app A (a x i) := by
  let e : F.obj H ≅ AddCommGrpCat.of (I →₀ ↥(F.obj A)) :=
    hF.coconePointUniqueUpToIso (finsupp_cofan_isColimit I (F.obj A))
  let d : Q.obj H ≅ AddCommGrpCat.of (I →₀ ↥(Q.obj A)) :=
    hQ.coconePointUniqueUpToIso (finsupp_cofan_isColimit I (Q.obj A))
  let m : AddCommGrpCat.of (I →₀ ↥(F.obj A)) ⟶ AddCommGrpCat.of (I →₀ ↥(Q.obj A)) :=
    AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom (ι := I) (τ.app A).hom)
  have he (i : I) : F.map (j i) ≫ e.hom =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := F.obj A) i) :=
    hF.comp_coconePointUniqueUpToIso_hom (finsupp_cofan_isColimit I (F.obj A)) ⟨i⟩
  have hd (i : I) : Q.map (j i) ≫ d.hom =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := Q.obj A) i) :=
    hQ.comp_coconePointUniqueUpToIso_hom (finsupp_cofan_isColimit I (Q.obj A)) ⟨i⟩
  have h : τ.app H ≫ d.hom = e.hom ≫ m := by
    apply hF.hom_ext
    rintro ⟨i⟩
    change F.map (j i) ≫ _ = F.map (j i) ≫ _
    rw [← Category.assoc, τ.naturality, Category.assoc, hd, ← Category.assoc, he]
    ext x k
    simp [m]
  refine ⟨e.addCommGroupIsoToAddEquiv, d.addCommGroupIsoToAddEquiv, ?_⟩
  intro x i
  exact congrArg (fun z ↦ z i) (ConcreteCategory.congr_hom h x)

namespace AlgebraicGeometry.Etale

/-- A single prime-field basis of Λ/pΛ gives direct-sum coordinates on both sides
of a cohomology pullback, and pullback acts separately on every coordinate.
Source: Stacks Project, Tags 03Q5 and 0739, together with the coefficient-basis
construction of `proposition-p-torsion-smooth-proper-curve--4`.
(blueprint: lem-pbc-constant-mod-cohomology-finsupp-pullback)

Proof: Give Λ/pΛ its canonical module structure over the lifted prime field
ULift (ZMod p), and choose a basis I. Its basis representation identifies the underlying
additive coefficient group with the direct sum of I copies of ULift (ZMod p).
Apply the constant abelian sheaf functor and its comparison with coefficient forgetting
to get the coproduct decomposition of the source sheaf. Express that coproduct as
the filtered colimit of its finite subcoproducts. On a qcqs scheme, Sheaf.H in degree q
preserves this colimit by the large filtered-colimit theorem, and its additive functor
preserves the finite biproducts. The colimit of these finite sums in abelian groups is
I →₀ H^q(X,Z/p); its universal property gives a. The inverse-image functor preserves
colimits, so the identical decomposition pulls back to Y. Apply the same argument
there to obtain b. Naturality of cohomologyMap with respect to each summand inclusion
makes the two maps agree on every single-coordinate class. Every finitely supported
family is a finite sum of such classes; additivity gives the coordinate equation.
The zero coefficient ring or zero quotient gives an empty I and zero groups. The
argument allows infinite bases, arbitrary q, and empty schemes, and needs no smoothness,
properness, characteristic assumption on the schemes, or bijectivity of pullback. -/
theorem exists_constantModSheaf_cohomology_finsupp_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : Y ⟶ X) (p : ℕ) [Fact p.Prime] (q : ℕ) :
    ∃ (I : Type (u + 1))
      (a : Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ X p)) q ≃+ (I →₀ Sheaf.H (X.constantZMod p) q))
      (b : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ X p))) q ≃+
        (I →₀ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj (X.constantZMod p)) q)),
      ∀ x i, b (cohomologyMap g
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (constantModSheaf Λ X p)) q x) i =
        cohomologyMap g (X.constantZMod p) q (a x i) := by
  classical
  let M := Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ)
  have hp : ∀ x : M, p • x = 0 := by
    intro x
    have hp0 : (p : M) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (p : Λ))
    rw [nsmul_eq_mul, hp0, zero_mul]
  let : Module (ZMod p) M := AddCommGroup.zmodModule hp
  let R := ULift.{u + 1} (ZMod p)
  let : Module R M := Module.compHom M ULift.ringEquiv.toRingHom
  let I := Module.Basis.ofVectorSpaceIndex R M
  let basis : Module.Basis I R M := Module.Basis.ofVectorSpace R M
  let a : I → ModuleCat.{u + 1} R := fun _ ↦ ModuleCat.of R R
  let T : ModuleCat.{u + 1} R ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let eM : (∐ a) ≅ ModuleCat.of R M :=
    (Limits.colimit.isColimit (Discrete.functor a)).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit R R I) ≪≫ basis.repr.symm.toModuleIso
  have : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    apply GrothendieckTopology.instPreservesSheafification
  let K := ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
    (constantModSheaf Λ X p))
  let A := X.constantZMod p
  let family : I → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun _ ↦ A
  let e : (∐ family) ≅ K :=
    (Limits.PreservesCoproduct.iso T a).symm ≪≫ T.mapIso eM ≪≫
      (constantCommuteCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm.app (ModuleCat.of Λ M)
  let F := Sheaf.functorH X.smallEtaleTopology q
  let U := upperStar AddCommGrpCat.{u + 1} g
  let Q := U ⋙ Sheaf.functorH Y.smallEtaleTopology q
  let τ : F ⟶ Q :=
    { app := fun L ↦ AddCommGrpCat.ofHom (cohomologyMap g L q)
      naturality := by
        intro L L' φ
        ext x
        exact cohomologyMap_map g q φ x }
  let c := Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone family
  have hc : Limits.IsColimit c :=
    Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone family
  obtain ⟨hcF⟩ := X.sheafH_isColimit_large_filtered hc q
  obtain ⟨hcQ⟩ := Y.sheafH_isColimit_large_filtered (Limits.isColimitOfPreserves U hc) q
  have hF := coproduct_preserved_of_finite_subcoproducts F family hcF
  have hQ := coproduct_preserved_of_finite_subcoproducts Q family hcQ
  obtain ⟨a₀, b₀, h⟩ := natural_finsupp_coordinates I (Limits.Sigma.ι family) F Q τ hF hQ
  let a₁ := (F.mapIso e.symm).addCommGroupIsoToAddEquiv.trans a₀
  let b₁ := (Q.mapIso e.symm).addCommGroupIsoToAddEquiv.trans b₀
  refine ⟨I, a₁, b₁, ?_⟩
  intro x i
  have hn := ConcreteCategory.congr_hom (τ.naturality e.inv) x
  change b₀ (Q.map e.inv (τ.app K x)) i = τ.app A (a₀ (F.map e.inv x) i)
  change τ.app (∐ family) (F.map e.inv x) = Q.map e.inv (τ.app K x) at hn
  rw [← hn]
  exact h (F.map e.inv x) i

end AlgebraicGeometry.Etale
