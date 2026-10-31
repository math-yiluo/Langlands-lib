import Langlands.AbelianScheme.SubalgebraDescentStatements
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation

/-! # Descent of group schemes to finitely generated subalgebras

The ported FLT theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`
descends a group law given on generalized points (FLT's `RelativeGroupLaw`). Here it is transferred
to group objects in `Over (Spec A)`, using FLT's correspondence between group objects and
`RelativeGroupLaw`s and a comparison of the group law of `Over.pullback` with the base change of
a `RelativeGroupLaw`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj CategoryTheory.Obj

noncomputable section

namespace Langlands.GroupScheme

section MonObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- A morphism of group objects that is multiplicative on generalized points is a morphism of
monoid objects. -/
theorem isMonHom_of_mul_comp {M N : C} [MonObj M] [GrpObj N] (f : M ⟶ N)
    (h : ∀ {X : C} (x y : X ⟶ M), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    have h1 := h (1 : 𝟙_ C ⟶ M) 1
    rw [mul_one] at h1
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact left_eq_mul.mp h1
  mul_hom := by
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, h, MonObj.comp_mul]
    simp

/-- Commutativity of a monoid object is transported along an isomorphism of monoid objects. -/
theorem isCommMonObj_of_iso [BraidedCategory C] {M N : C} [MonObj M] [MonObj N] (e : M ≅ N)
    [IsMonHom e.hom] [IsCommMonObj M] : IsCommMonObj N := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' ≫ e.hom := ⟨a ≫ e.inv, by simp⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' ≫ e.hom := ⟨b ≫ e.inv, by simp⟩
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm a']

end MonObj

section BaseChange

variable {S S' : Scheme.{u}} (ψ : S' ⟶ S)

/-- The point of `Y` over `S` underlying a point of the base change of `Y` along `ψ`, given by
the adjunction between `Over.map ψ` and `Over.pullback ψ`. -/
def basePoint {Y : Over S} {U : Over S'} (z : U ⟶ (Over.pullback ψ).obj Y) :
    Over.mk (U.hom ≫ ψ) ⟶ Y :=
  ((Over.mapPullbackAdj ψ).homEquiv U Y).symm z

theorem basePoint_left {Y : Over S} {U : Over S'} (z : U ⟶ (Over.pullback ψ).obj Y) :
    (basePoint ψ z).left = z.left ≫ pullback.fst Y.hom ψ :=
  rfl

theorem homEquiv_left_fst {Y : Over S} {U : Over S'} (b : (Over.map ψ).obj U ⟶ Y) :
    ((Over.mapPullbackAdj ψ).homEquiv U Y b).left ≫ pullback.fst Y.hom ψ = b.left := by
  have h := basePoint_left ψ ((Over.mapPullbackAdj ψ).homEquiv U Y b)
  simp only [basePoint, Equiv.symm_apply_apply] at h
  exact h.symm

/-- The adjunction bijection for `Over.map ψ ⊣ Over.pullback ψ` is multiplicative. -/
theorem mapPullbackAdj_homEquiv_mul {Y : Over S} [GrpObj Y] {U : Over S'}
    (b₁ b₂ : (Over.map ψ).obj U ⟶ Y) :
    (Over.mapPullbackAdj ψ).homEquiv U Y (b₁ * b₂) =
      (Over.mapPullbackAdj ψ).homEquiv U Y b₁ * (Over.mapPullbackAdj ψ).homEquiv U Y b₂ := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- The group law of a base change, read off on the underlying points of the original group
object. -/
theorem mul_left_fst {Y : Over S} [GrpObj Y] {U : Over S'}
    (z₁ z₂ : U ⟶ (Over.pullback ψ).obj Y) :
    (z₁ * z₂).left ≫ pullback.fst Y.hom ψ = (basePoint ψ z₁ * basePoint ψ z₂).left := by
  have h := mapPullbackAdj_homEquiv_mul ψ (basePoint ψ z₁) (basePoint ψ z₂)
  simp only [basePoint, Equiv.apply_symm_apply] at h
  rw [← h]
  exact homEquiv_left_fst ψ _

end BaseChange

/-- Descent of group schemes to finitely generated subalgebras. -/
theorem subalgebraDescent : GroupScheme.SubalgebraDescentStatement.{u} := by
  intro A₀ _ A _ _ X₀ f₀ _ _ _ G a hP s
  -- Transport the group structure of `G` to the fibre product `X₀ ×_{A₀} A`.
  let p := pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
  let eO : G.X ≅ Over.mk p := Over.isoMk hP.isoPullback (by simp [p])
  let : GrpObj (Over.mk p) := GrpObj.ofIso eO
  have : IsMonHom eO.hom := isMonHom_ofIso eO
  let L : RelativeGroupLaw A p := relativeGroupLawOfGrpObj A p
  obtain ⟨T, hT, hs, Lₜ, c, hciso, hc, -, hmul, hcomm⟩ :=
    RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      f₀ L s
  let pT := pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))
  let ψ := Spec.map (CommRingCat.ofHom (algebraMap ↥T A))
  let : GrpObj (Over.mk pT) := Lₜ.grpObjOverMk
  let G₀ : GroupScheme (Spec (CommRingCat.of ↥T)) := Grp.mk (Over.mk pT)
  refine ⟨T, hT, hs, G₀, pullback.fst _ _, IsPullback.of_hasPullback _ _, ?_, ?_⟩
  · intro hG
    have : IsCommMonObj (Over.mk p) := isCommMonObj_of_iso eO
    have hL : L.IsCommutative := fun t x y =>
      relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj inferInstance t x y
    exact Lₜ.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr (fun t x y => hcomm hL t x y)
  · let cO : Over.mk p ≅ ((GroupScheme.baseChange ψ).obj G₀).X :=
      Over.isoMk (@asIso _ _ _ _ c hciso) hc
    have hcO : ∀ {X : Over (Spec (CommRingCat.of A))} (x y : X ⟶ Over.mk p),
        (x * y) ≫ cO.hom = (x ≫ cO.hom) * (y ≫ cO.hom) := by
      intro X x y
      ext1
      refine pullback.hom_ext (f := pT) (g := ψ) ?_ ?_
      · calc ((x * y) ≫ cO.hom).left ≫ pullback.fst pT ψ
            = ((L.mul X.hom ⟨x.left, Over.w x⟩ ⟨y.left, Over.w y⟩).1 ≫ c) ≫
                pullback.fst pT ψ := rfl
          _ = ((Lₜ.baseChange ψ).mul X.hom ⟨x.left ≫ c, by rw [Category.assoc, hc]; exact Over.w x⟩
                ⟨y.left ≫ c, by rw [Category.assoc, hc]; exact Over.w y⟩).1 ≫
                pullback.fst pT ψ := by rw [hmul]
          _ = (Lₜ.mul (X.hom ≫ ψ)
                (RelativeGroupLaw.baseChangePointToBase ψ
                  ⟨x.left ≫ c, by rw [Category.assoc, hc]; exact Over.w x⟩)
                (RelativeGroupLaw.baseChangePointToBase ψ
                  ⟨y.left ≫ c, by rw [Category.assoc, hc]; exact Over.w y⟩)).1 := by
              rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
                pullback.lift_fst]
          _ = (Lₜ.mul (X.hom ≫ ψ) (overHomToSchemeHomOver (basePoint ψ (x ≫ cO.hom)))
                (overHomToSchemeHomOver (basePoint ψ (y ≫ cO.hom)))).1 := rfl
          _ = (basePoint ψ (x ≫ cO.hom) * basePoint ψ (y ≫ cO.hom)).left := by
              rw [← Lₜ.overHomToSchemeHomOver_mul]
              rfl
          _ = ((x ≫ cO.hom) * (y ≫ cO.hom)).left ≫ pullback.fst pT ψ :=
              (mul_left_fst ψ (x ≫ cO.hom) (y ≫ cO.hom)).symm
      · have h₁ := Over.w ((x * y) ≫ cO.hom)
        have h₂ := Over.w ((x ≫ cO.hom) * (y ≫ cO.hom))
        exact h₁.trans h₂.symm
    let Φ := eO ≪≫ cO
    have hΦ : ∀ {X : Over (Spec (CommRingCat.of A))} (x y : X ⟶ G.X),
        (x * y) ≫ Φ.hom = (x ≫ Φ.hom) * (y ≫ Φ.hom) := by
      intro X x y
      simp only [Φ, Iso.trans_hom, ← Category.assoc]
      rw [MonObj.mul_comp, hcO]
    have : IsMonHom Φ.hom := isMonHom_of_mul_comp Φ.hom hΦ
    exact ⟨Grp.mkIso Φ (IsMonHom.one_hom Φ.hom) (IsMonHom.mul_hom Φ.hom)⟩

end Langlands.GroupScheme

end
