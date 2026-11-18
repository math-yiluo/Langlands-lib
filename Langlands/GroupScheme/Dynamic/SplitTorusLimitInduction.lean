import Langlands.GroupScheme.Dynamic.SchemeActionLimit
import Langlands.GroupScheme.Dynamic.ProperAffineExtension
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Limit induction for split torus actions on proper schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitTorusLimitInduction

open SchemeAction

section General

variable {S : Scheme.{u}} {T : CommGroupScheme S} {X : Over S} (a : SchemeAction T.toGrp X)

/-- **Limits preserve fixedness under a commuting cocharacter.** If `w` is fixed by the
action restricted along `ν'`, then the limit of `w` along `ν` is again fixed by it. -/
theorem isFixed_evalZero_of_isFixed [IsSeparated X.hom] {ν ν' : cocharacterLattice T}
    {Z : Over S} {w : Z ⟶ X} {e : Z ⊗ AffineLine.scheme S ⟶ X}
    (he : (a.restrict (CommGroupScheme.groupHom ν)).IsGmOrbitExtension w e)
    (hw : (a.restrict (CommGroupScheme.groupHom ν')).IsFixed w) :
    (a.restrict (CommGroupScheme.groupHom ν')).IsFixed (Dynamic.evalZero e) := by
  rw [isFixed_iff_universal]
  have he₁ := he.whiskerRight _ (fst Z (Gm S).X)
  have he₂ : (a.restrict (CommGroupScheme.groupHom ν)).IsGmOrbitExtension
      (fst Z (Gm S).X ≫ w)
      ((a.restrict (CommGroupScheme.groupHom ν')).act (fst _ _ ≫ snd Z (Gm S).X)
        (fst Z (Gm S).X ▷ AffineLine.scheme S ≫ e)) := by
    unfold IsGmOrbitExtension
    rw [naturality, whiskerLeft_fst_assoc, he₁]
    simp only [gmOrbit, restrict_act]
    rw [← act_mul, mul_comm, act_mul]
    congr 1
    simpa only [restrict_act, Category.assoc] using
      hw _ (fst _ _ ≫ fst Z (Gm S).X) (fst _ _ ≫ snd Z (Gm S).X)
  have huniq := he₂.unique _ he₁
  have h0 := congrArg Dynamic.evalZero huniq
  rw [Dynamic.evalZero_whiskerRight] at h0
  have h3 : Dynamic.evalZero ((a.restrict (CommGroupScheme.groupHom ν')).act
      (fst _ _ ≫ snd Z (Gm S).X) (fst Z (Gm S).X ▷ AffineLine.scheme S ≫ e)) =
      (a.restrict (CommGroupScheme.groupHom ν')).act (snd Z (Gm S).X)
        (fst Z (Gm S).X ≫ Dynamic.evalZero e) := by
    rw [← Dynamic.evalZero_whiskerRight]
    unfold Dynamic.evalZero
    rw [naturality, lift_fst_assoc, Category.id_comp]
  rw [← h3, h0]

/-- **Fixedness is detected on a basis of cocharacters.** For a split torus `T ≅ 𝔾ₘ^I`, a
point fixed by the action restricted along each coordinate cocharacter is fixed by `T`. -/
theorem isFixed_of_forall {I : Type u} [Fintype I]
    (eC : T ≅ splitTorus.commGroupScheme S I) {Z : Over S} {x : Z ⟶ X}
    (hx : ∀ j, (a.restrict
      (CommGroupScheme.groupHom (splitTorus.single S I j ≫ eC.inv))).IsFixed x) :
    a.IsFixed x := by
  classical
  intro T' c h
  have h1 : (∑ j, (eC.hom ≫ splitTorus.proj S I j) ≫ (splitTorus.single S I j ≫ eC.inv)) =
      𝟙 T := by
    have h2 : eC.hom ≫ (∑ j, splitTorus.proj S I j ≫ splitTorus.single S I j) ≫ eC.inv =
        ∑ j, (eC.hom ≫ splitTorus.proj S I j) ≫ (splitTorus.single S I j ≫ eC.inv) := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    rw [← h2, splitTorus.sum_proj_comp_single, Category.id_comp, Iso.hom_inv_id]
  have key : ∀ s : Finset I, a.act (∏ j ∈ s, h ≫ (CommGroupScheme.groupHom
      ((eC.hom ≫ splitTorus.proj S I j) ≫ (splitTorus.single S I j ≫ eC.inv))).hom.hom)
      (c ≫ x) = c ≫ x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, act_one]
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, act_mul, ih, comp_groupHom_comp]
      have := hx j T' c (h ≫ (CommGroupScheme.groupHom (eC.hom ≫ splitTorus.proj S I j)).hom.hom)
      rwa [restrict_act] at this
  have h2 := key Finset.univ
  rw [← comp_groupHom_sum, h1] at h2
  exact h2

end General

section Normalized

variable {S : Scheme.{u}} {G : GroupScheme S} {X : Over S} (a : SchemeAction G X)

/-- **Limits preserve fixedness under a normalized subgroup.** Let `ψ` be a cocharacter of
`G` and `j : U ⟶ G` a subgroup normalized by `ψ`. If `w` is fixed by `U`, then the limit of
`w` along `ψ` is again fixed by `U`. -/
theorem isFixed_evalZero_of_normalizes [IsSeparated X.hom] (ψ : (Gm S).toGrp ⟶ G)
    {U : GroupScheme S} (j : U ⟶ G)
    (hnorm : ∀ (Q : Over S) (s : Q ⟶ (Gm S).X) (v : Q ⟶ U.X), ∃ v' : Q ⟶ U.X,
      v' ≫ j.hom.hom = (s ≫ ψ.hom.hom)⁻¹ * (v ≫ j.hom.hom) * (s ≫ ψ.hom.hom))
    {Z : Over S} {w : Z ⟶ X} {e : Z ⊗ AffineLine.scheme S ⟶ X}
    (he : (a.restrict ψ).IsGmOrbitExtension w e) (hw : (a.restrict j).IsFixed w) :
    (a.restrict j).IsFixed (Dynamic.evalZero e) := by
  rw [isFixed_iff_universal]
  have he₁ := he.whiskerRight _ (fst Z U.X)
  have he₂ : (a.restrict ψ).IsGmOrbitExtension (fst Z U.X ≫ w)
      ((a.restrict j).act (fst _ _ ≫ snd Z U.X) (fst Z U.X ▷ AffineLine.scheme S ≫ e)) := by
    unfold IsGmOrbitExtension
    rw [naturality, whiskerLeft_fst_assoc, he₁]
    simp only [gmOrbit, restrict_act]
    obtain ⟨v', hv'⟩ := hnorm _ (snd _ _) (fst _ _ ≫ snd Z U.X)
    have hmul : ((fst _ _ ≫ snd Z U.X) ≫ j.hom.hom) * (snd (Z ⊗ U.X) (Gm S).X ≫ ψ.hom.hom) =
        (snd (Z ⊗ U.X) (Gm S).X ≫ ψ.hom.hom) * (v' ≫ j.hom.hom) := by
      rw [hv']
      group
    rw [← act_mul, hmul, act_mul]
    congr 1
    simpa only [restrict_act, Category.assoc] using hw _ (fst _ _ ≫ fst Z U.X) v'
  have huniq := he₂.unique _ he₁
  have h0 := congrArg Dynamic.evalZero huniq
  rw [Dynamic.evalZero_whiskerRight] at h0
  have h3 : Dynamic.evalZero ((a.restrict j).act
      (fst _ _ ≫ snd Z U.X) (fst Z U.X ▷ AffineLine.scheme S ≫ e)) =
      (a.restrict j).act (snd Z U.X) (fst Z U.X ≫ Dynamic.evalZero e) := by
    rw [← Dynamic.evalZero_whiskerRight]
    unfold Dynamic.evalZero
    rw [naturality, lift_fst_assoc, Category.id_comp]
  rw [← h3, h0]

end Normalized

section Field

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom] (a : SchemeAction T.toGrp X)

/-- Every rational point of a proper scheme has a limit along every cocharacter. -/
theorem exists_isGmOrbitExtension (ν : cocharacterLattice T)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    ∃ e, (a.restrict (CommGroupScheme.groupHom ν)).IsGmOrbitExtension w e :=
  AffineLine.exists_extension_of_isProper X _

/-- **Limit induction.** Let a split torus `T` act on a proper scheme `X` over a field, and let
`P` and `R` be properties of rational points. Suppose `P` passes to limits along every
cocharacter, `R` passes back from a limit to a point satisfying `P`, and every `T`-fixed point
satisfying `P` satisfies `R`. Then every rational point satisfying `P` satisfies `R`. -/
theorem limit_induction (hT : IsSplitTorus T.toGrp)
    (P R : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) → Prop)
    (hP : ∀ (ν : cocharacterLattice T) (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
      (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶
        X),
      (a.restrict (CommGroupScheme.groupHom ν)).IsGmOrbitExtension w e → P w →
        P (Dynamic.evalZero e))
    (hR : ∀ (ν : cocharacterLattice T) (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
      (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶
        X),
      (a.restrict (CommGroupScheme.groupHom ν)).IsGmOrbitExtension w e → P w →
        R (Dynamic.evalZero e) → R w)
    (hfix : ∀ w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed w → P w → R w)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) (hw : P w) : R w := by
  classical
  obtain ⟨I, hI, ⟨eG⟩⟩ := hT
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso eG
  let ν : I → cocharacterLattice T := fun j ↦ splitTorus.single _ I j ≫ eC.inv
  have key : ∀ F : Finset I, ∀ w, P w →
      (∀ j ∉ F, (a.restrict (CommGroupScheme.groupHom (ν j))).IsFixed w) → R w := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro w hw hfx
      exact hfix w (isFixed_of_forall a eC fun j ↦ hfx j (by simp)) hw
    | insert j F hj ih =>
      intro w hw hfx
      obtain ⟨e, he⟩ := exists_isGmOrbitExtension a (ν j) w
      apply hR (ν j) w e he hw
      apply ih _ (hP (ν j) w e he hw)
      intro i hi
      by_cases hij : i = j
      · subst hij
        exact he.isFixed_evalZero _
      · exact isFixed_evalZero_of_isFixed a he (hfx i (by simp [hij, hi]))
  exact key Finset.univ w hw (fun j hj ↦ absurd (Finset.mem_univ j) hj)

end Field

end Langlands.GroupScheme.SplitTorusLimitInduction
