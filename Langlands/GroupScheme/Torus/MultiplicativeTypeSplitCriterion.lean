import Langlands.GroupScheme.Torus.DiagonalizableUniversalSubtorus
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Torus.IsomorphismLocusEtale
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.HomScheme.GraphBaseChange
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent

/-! # A splitting criterion from a universal subtorus and a finite part -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-! ### Product homomorphisms -/

section ProdHom

variable {S : Scheme.{u}} {A B M : GroupScheme S}

/-- In a commutative group scheme, the values of any two homomorphisms commute. -/
theorem commute_of_isCommMonObj [IsCommMonObj M.X] (a : A ⟶ M) (b : B ⟶ M) (T : Over S)
    (x : T ⟶ A.X) (y : T ⟶ B.X) : Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom) := by
  let := Hom.commMonoid (X := T) (M := M.X)
  exact mul_comm _ _

/-- The underlying morphism of `prodHom a b` is the pointwise product of
`fst ≫ a` and `snd ≫ b`. -/
theorem prodHom_hom_hom (a : A ⟶ M) (b : B ⟶ M) (hab) :
    (prodHom a b hab).hom.hom = (fst A.X B.X ≫ a.hom.hom) * (snd A.X B.X ≫ b.hom.hom) := by
  have h := comp_prodHom a b hab (A ⊗ B).X (𝟙 _)
  rw [Category.id_comp] at h
  exact h

/-- `prodHom` depends only on its two homomorphisms. -/
theorem prodHom_congr {a a' : A ⟶ M} {b b' : B ⟶ M} (ha : a = a') (hb : b = b') (hab hab') :
    prodHom a b hab = prodHom a' b' hab' := by
  subst ha hb
  rfl

/-- Postcomposing a product homomorphism with a homomorphism. -/
theorem prodHom_comp {N : GroupScheme S} (a : A ⟶ M) (b : B ⟶ M) (f : M ⟶ N) (hab hab') :
    prodHom a b hab ≫ f = prodHom (a ≫ f) (b ≫ f) hab' := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom, comp_prodHom, MonObj.mul_comp,
    Grp.comp_hom_hom, Grp.comp_hom_hom, Category.assoc, Category.assoc]

/-- Precomposing a product homomorphism with a product of homomorphisms. -/
theorem tensorHom_prodHom {A' B' : GroupScheme S} (f : A' ⟶ A) (g : B' ⟶ B)
    (a : A ⟶ M) (b : B ⟶ M) (hab hab') :
    (f ⊗ₘ g) ≫ prodHom a b hab = prodHom (f ≫ a) (g ≫ b) hab' := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, prodHom_hom_hom, prodHom_hom_hom, MonObj.comp_mul,
    Grp.comp_hom_hom, Grp.comp_hom_hom]
  change ((f.hom.hom ⊗ₘ g.hom.hom) ≫ fst A.X B.X ≫ a.hom.hom) *
      ((f.hom.hom ⊗ₘ g.hom.hom) ≫ snd A.X B.X ≫ b.hom.hom) = _
  rw [tensorHom_fst_assoc, tensorHom_snd_assoc]

/-- Base change commutes with product homomorphisms. -/
theorem baseChange_prodHom_inv {S' : Scheme.{u}} (q : S' ⟶ S) (a : A ⟶ M) (b : B ⟶ M)
    (hab hab') :
    (baseChangeTensorIso q A B).inv ≫ (baseChange q).map (prodHom a b hab) =
      prodHom ((baseChange q).map a) ((baseChange q).map b) hab' := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, prodHom_hom_hom]
  change (baseChangeTensorIso q A B).inv.hom.hom ≫
      (Over.pullback q).map (prodHom a b hab).hom.hom = _
  have h₁ : (baseChangeTensorIso q A B).inv.hom.hom ≫ (Over.pullback q).map (fst A.X B.X) =
      fst ((baseChange q).obj A).X ((baseChange q).obj B).X :=
    congrArg (fun f => f.hom.hom) (baseChangeTensorIso_inv_map_fst q A B)
  have h₂ : (baseChangeTensorIso q A B).inv.hom.hom ≫ (Over.pullback q).map (snd A.X B.X) =
      snd ((baseChange q).obj A).X ((baseChange q).obj B).X :=
    congrArg (fun f => f.hom.hom) (baseChangeTensorIso_inv_map_snd q A B)
  rw [prodHom_hom_hom, Functor.map_mul, MonObj.comp_mul, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  erw [h₁, h₂]
  rfl

end ProdHom

/-! ### Two universal subtori of the same group -/

/-- Two universal subtori of the same group scheme have isomorphic sources, compatibly with
the inclusions. -/
theorem IsUniversalSubtorus.exists_iso {S : Scheme.{u}} {H T₁ T₂ : GroupScheme S}
    {j₁ : T₁ ⟶ H} {j₂ : T₂ ⟶ H} (h₁ : IsUniversalSubtorus j₁) (h₂ : IsUniversalSubtorus j₂) :
    ∃ g : T₁ ≅ T₂, g.hom ≫ j₂ = j₁ := by
  obtain ⟨a, ha⟩ := h₂.factor j₁ h₁.2.1
  obtain ⟨c, hc⟩ := h₁.factor j₂ h₂.2.1
  have : Mono j₁.hom.hom := h₁.1.mono_overHom
  have : Mono j₂.hom.hom := h₂.1.mono_overHom
  have hac : a ≫ c = 𝟙 T₁ := by
    apply Grp.hom_ext
    rw [← cancel_mono j₁.hom.hom, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, hc,
      ha, Category.id_comp]
  have hca : c ≫ a = 𝟙 T₂ := by
    apply Grp.hom_ext
    rw [← cancel_mono j₂.hom.hom, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, ha,
      hc, Category.id_comp]
  exact ⟨⟨a, c, hac, hca⟩, ha⟩

/-! ### The model decomposition `D(Λ) ≅ D(I → ℤ) × D(A)` -/

namespace Diagonalizable

variable (R : CommRingCat.{u}) {Λ I A : Type u} [AddCommGroup Λ] [AddCommGroup A]
  (e : Λ ≃+ (I → ℤ) × A)

/-- The inclusion `D(A) ⟶ D(Λ)` of the finite-character factor, induced by the projection
`Λ ⟶ A` given by `e`. -/
def finiteInclusion : (groupScheme R A).toGrp ⟶ (groupScheme R Λ).toGrp :=
  restrictMap R ((AddMonoidHom.snd (I → ℤ) A).comp e.toAddMonoidHom)

/-- `D(I → ℤ) × D(A) ⟶ D(Λ)`, `(x, y) ↦ x * y`, is an isomorphism. -/
theorem isIso_prodHom_freeInclusion_finiteInclusion :
    IsIso (prodHom (freeInclusion R e) (finiteInclusion R e)
      (commute_of_isCommMonObj _ _)) := by
  let φ := congrIso R e ≪≫ productIso R (I → ℤ) A
  have h : φ.hom ≫ prodHom (freeInclusion R e) (finiteInclusion R e)
      (commute_of_isCommMonObj _ _) = 𝟙 _ := by
    apply hom_ext_points
    intro T x
    rw [Grp.comp_hom_hom, Grp.id_hom_hom, Category.comp_id, ← Category.assoc, comp_prodHom]
    apply (characterPointsEquiv R Λ T).injective
    apply MonoidHom.ext
    intro l
    rw [map_mul, MonoidHom.mul_apply]
    let w := x ≫ (congrIso R e).hom.hom.hom
    have hprod := isoOfPointModels_hom (fun T : Over (Spec R) =>
        (Multiplicative (I → ℤ) →* (Γ(T.left, ⊤))ˣ) × (Multiplicative A →* (Γ(T.left, ⊤))ˣ))
      (fun a => productCharacterRestrict R (I → ℤ) A a)
      (productCharacterPointsEquiv R (I → ℤ) A) (tensorCharacterPointsEquiv R (I → ℤ) A)
      (productCharacterPointsEquiv_naturality R (I → ℤ) A)
      (tensorCharacterPointsEquiv_naturality R (I → ℤ) A) T w
    have hx : x ≫ φ.hom.hom.hom = w ≫ (productIso R (I → ℤ) A).hom.hom.hom :=
      (Category.assoc _ _ _).symm
    have h₁ : characterPointsEquiv R Λ T
        ((productPointsEquiv _ _ T (x ≫ φ.hom.hom.hom)).1 ≫ (freeInclusion R e).hom.hom) l =
        characterPointsEquiv R Λ T x (.ofAdd (e.symm ((e l.toAdd).1, 0))) := by
      rw [hx]
      refine (pointsEquiv_restrictMap R _ _ l.toAdd).trans ?_
      have h := congrArg (fun p => p.1 (.ofAdd (e l.toAdd).1)) hprod
      refine h.trans ?_
      exact congrIso_hom R e T x ((e l.toAdd).1, 0)
    have h₂ : characterPointsEquiv R Λ T
        ((productPointsEquiv _ _ T (x ≫ φ.hom.hom.hom)).2 ≫ (finiteInclusion R e).hom.hom) l =
        characterPointsEquiv R Λ T x (.ofAdd (e.symm (0, (e l.toAdd).2))) := by
      rw [hx]
      refine (pointsEquiv_restrictMap R _ _ l.toAdd).trans ?_
      have h := congrArg (fun p => p.2 (.ofAdd (e l.toAdd).2)) hprod
      refine h.trans ?_
      exact congrIso_hom R e T x (0, (e l.toAdd).2)
    rw [h₁, h₂, ← map_mul]
    congr 1
    change Multiplicative.ofAdd (e.symm ((e l.toAdd).1, 0) + e.symm (0, (e l.toAdd).2)) = l
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    rfl
  have hP : prodHom (freeInclusion R e) (finiteInclusion R e) (commute_of_isCommMonObj _ _) =
      φ.inv := (Iso.hom_comp_eq_id φ).1 h
  rw [hP]
  infer_instance

/-! ### The model decomposition over an arbitrary scheme -/

/-- The inclusion `D_Y(A) ⟶ D_Y(Λ)` of the finite-character factor over a scheme `Y`, induced
by the projection `Λ ⟶ A` given by `e`. It is the base change of `finiteInclusion` from
`Spec ℤ`, as `freeInclusionOverScheme` is for the free factor. -/
def finiteInclusionOverScheme (Y : Scheme.{u}) {Λ I A : Type u} [AddCommGroup Λ]
    [AddCommGroup A] (e : Λ ≃+ (I → ℤ) × A) :
    RelativeMultiplicativeType.diagonalizable Y A ⟶
      RelativeMultiplicativeType.diagonalizable Y Λ :=
  (GroupScheme.baseChange (Gm.toSpecZ Y)).map
    (finiteInclusion (CommRingCat.of (ULift.{u} ℤ)) e)

/-- Diagonalizable groups over a scheme are commutative. -/
instance isCommMonObj_diagonalizable (Y : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] :
    IsCommMonObj (RelativeMultiplicativeType.diagonalizable Y Λ).X :=
  Functor.isCommMonObj_obj (F := Over.pullback (Gm.toSpecZ Y))
    (M := (groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).toGrp.X)

/-- Over every scheme `Y`, `D_Y(I → ℤ) × D_Y(A) ⟶ D_Y(Λ)`, `(x, y) ↦ x * y`, is an
isomorphism. -/
theorem isIso_prodHom_freeInclusionOverScheme_finiteInclusionOverScheme (Y : Scheme.{u})
    {Λ I A : Type u} [AddCommGroup Λ] [AddCommGroup A] (e : Λ ≃+ (I → ℤ) × A) :
    IsIso (prodHom (freeInclusionOverScheme Y e) (finiteInclusionOverScheme Y e)
      (commute_of_isCommMonObj _ _)) := by
  let R := CommRingCat.of (ULift.{u} ℤ)
  have h := baseChange_prodHom_inv (Gm.toSpecZ Y) (freeInclusion R e) (finiteInclusion R e)
    (commute_of_isCommMonObj _ _) (commute_of_isCommMonObj _ _)
  have : IsIso (prodHom (freeInclusion R e) (finiteInclusion R e)
      (commute_of_isCommMonObj _ _)) := isIso_prodHom_freeInclusion_finiteInclusion R e
  change IsIso (prodHom ((GroupScheme.baseChange (Gm.toSpecZ Y)).map (freeInclusion R e))
    ((GroupScheme.baseChange (Gm.toSpecZ Y)).map (finiteInclusion R e)) _)
  rw [← h]
  infer_instance

end Diagonalizable

/-! ### The splitting criterion -/

open RelativeMultiplicativeType Diagonalizable in
/-- **Splitting criterion.** Let `G` be a commutative group scheme over `X` with a universal
subtorus `τ : D_X(I' → ℤ) ⟶ G` and a homomorphism `σ : D_X(A) ⟶ G` from a finite diagonalizable
group. Suppose that after a surjective flat locally finitely presented base change `q : W ⟶ X`
there is an isomorphism `ψ : G_W ≅ D_W(Λ)`, with `Λ ≅ (I → ℤ) × A`, under which `σ_W` becomes
the inclusion of the finite factor `D_W(A)`. Then `G ≅ D_X((I' → ℤ) × A)`, so `G` is
diagonalizable. -/
theorem isDiagonalizable_of_split_parts {X W : Scheme.{u}} (q : W ⟶ X) [Surjective q] [Flat q]
    [LocallyOfFinitePresentation q] {G : GroupScheme X}
    {I' I A Λ : Type u} [Fintype I'] [DecidableEq I'] [Fintype I] [DecidableEq I]
    [AddCommGroup A] [Finite A] [AddCommGroup Λ] (e : Λ ≃+ (I → ℤ) × A)
    (τ : diagonalizable X (I' → ℤ) ⟶ G) (hτ : IsUniversalSubtorus τ)
    (σ : diagonalizable X A ⟶ G)
    (ψ : (GroupScheme.baseChange q).obj G ≅ diagonalizable W Λ)
    (hσ : (diagonalizableBaseChangeIso q A).inv ≫ (GroupScheme.baseChange q).map σ ≫ ψ.hom =
      finiteInclusionOverScheme W e) :
    IsDiagonalizable G := by
  let R := CommRingCat.of (ULift.{u} ℤ)
  let F := GroupScheme.baseChange q
  -- `G_W ≅ D_W(Λ)` is commutative, and commutativity descends along the fppf cover `q`.
  have hGW : IsCommMonObj (F.obj G).X := by
    apply (isCommMonObj_iff_isMulCommutative _).2
    intro U
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (isoPointsEquiv ψ U).injective
    rw [map_mul, map_mul, mul_comm]
  have : IsCommMonObj G.X :=
    isCommMonObj_of_fppfCover
      (Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) PUnit.{u + 1}
        (fun _ => W) (fun _ => q) (fun x => ⟨⟨⟩, q.surjective x⟩)
        (fun _ => ⟨inferInstance, inferInstance⟩))
      (fun _ => hGW)
  let Ψ := prodHom τ σ (commute_of_isCommMonObj _ _)
  -- The universal subtorus of `D_W(Λ)` obtained from `τ`.
  let τW := (diagonalizableBaseChangeIso q (I' → ℤ)).inv ≫ F.map τ ≫ ψ.hom
  have hτW : IsUniversalSubtorus τW := by
    have h₁ := (hτ.baseChange q).comp_iso ψ
    exact h₁.iso_comp (diagonalizableBaseChangeIso q (I' → ℤ)).symm
  obtain ⟨g, hg⟩ := IsUniversalSubtorus.exists_iso hτW
    (isUniversalSubtorus_freeInclusionOverScheme W e)
  have key : ((diagonalizableBaseChangeIso q (I' → ℤ)).inv ⊗ₘ
      (diagonalizableBaseChangeIso q A).inv) ≫ (baseChangeTensorIso q _ _).inv ≫
        F.map Ψ ≫ ψ.hom =
      (g.hom ⊗ₘ 𝟙 _) ≫ prodHom (freeInclusionOverScheme W e) (finiteInclusionOverScheme W e)
        (commute_of_isCommMonObj _ _) := by
    rw [reassoc_of% (baseChange_prodHom_inv q τ σ (commute_of_isCommMonObj _ _)
        (commute_of_isCommMonObj _ _)),
      prodHom_comp _ _ _ _ (commute_of_isCommMonObj _ _),
      tensorHom_prodHom _ _ _ _ _ (commute_of_isCommMonObj _ _),
      tensorHom_prodHom _ _ _ _ _ (commute_of_isCommMonObj _ _)]
    apply prodHom_congr
    · rw [hg]
    · rw [Category.id_comp, ← hσ]
  have hmodel := isIso_prodHom_freeInclusionOverScheme_finiteInclusionOverScheme W e
  have h₀ : IsIso (((diagonalizableBaseChangeIso q (I' → ℤ)).inv ⊗ₘ
      (diagonalizableBaseChangeIso q A).inv) ≫ (baseChangeTensorIso q _ _).inv ≫
        F.map Ψ ≫ ψ.hom) := by
    rw [key]
    infer_instance
  have h₁ : IsIso ((baseChangeTensorIso q _ _).inv ≫ F.map Ψ ≫ ψ.hom) :=
    IsIso.of_isIso_comp_left ((diagonalizableBaseChangeIso q (I' → ℤ)).inv ⊗ₘ
      (diagonalizableBaseChangeIso q A).inv) _
  have h₂ : IsIso (F.map Ψ ≫ ψ.hom) :=
    IsIso.of_isIso_comp_left (baseChangeTensorIso q _ _).inv _
  have h₃ : IsIso (F.map Ψ) := IsIso.of_isIso_comp_right _ ψ.hom
  have : IsIso Ψ := TorusIsomorphismLocus.isIso_of_fppf_baseChange q Ψ
  have hfg : AddGroup.FG ((I' → ℤ) × A) := by
    rw [← Module.Finite.iff_addGroup_fg]
    infer_instance
  exact ⟨(I' → ℤ) × A, inferInstance, hfg, ⟨(asIso Ψ).symm ≪≫
    (baseChangeTensorIso (Gm.toSpecZ X) _ _).symm ≪≫
      (GroupScheme.baseChange (Gm.toSpecZ X)).mapIso (productIso R (I' → ℤ) A).symm⟩⟩

end Langlands.GroupScheme
