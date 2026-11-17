import Langlands.GroupScheme.Torus.HomFamilyRigidity
import Langlands.GroupScheme.Torus.ExponentHomomorphisms

/-! # Detecting homomorphisms of split tori on one fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem hom_eq_on_factoring_test
    {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}
    {f g : G ⟶ H}
    (hfg : (baseChange b).map f = (baseChange b).map g)
    (V : Over S) (a : V.left ⟶ S') (ha : a ≫ b = V.hom)
    (t : V ⟶ G.X) :
    t ≫ f.hom.hom = t ≫ g.hom.hom := by
  let W : Over S' := Over.mk a
  let t' : (Over.map b).obj W ⟶ G.X :=
    Over.homMk t.left (by
      change t.left ≫ G.X.hom = a ≫ b
      rw [ha]
      exact Over.w t)
  obtain ⟨y, hy⟩ := (baseChangePointsEquiv b G W).surjective t'
  have h : t' ≫ f.hom.hom = t' ≫ g.hom.hom := by
    rw [← hy, ← baseChangePointsEquiv_comp, ← baseChangePointsEquiv_comp, hfg]
  exact Over.OverMorphism.ext (congrArg (fun z => z.left) h)

namespace splitTorus

/-- The integral character pullback of the canonically identified field fibre
of an actual coordinate split-torus homomorphism. -/
def fieldFibreCharacterMap
    {S : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (f : splitTorus S I ⟶ splitTorus S J) : (J → ℤ) →ₗ[ℤ] (I → ℤ) :=
  characterMap I J
    ((baseChangeIso b I).inv ≫ (baseChange b).map f ≫ (baseChangeIso b J).hom)

variable {S : Scheme.{u}} [PreconnectedSpace S]
  {I J : Type u} [Fintype I] [Fintype J]

/-- Over a preconnected scheme, equality at one field-valued point detects
equality of homomorphisms between coordinate split tori. -/
theorem hom_eq_of_field_baseChange
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    {f g : splitTorus S I ⟶ splitTorus S J}
    (hfg : (baseChange b).map f = (baseChange b).map g) : f = g := by
  classical
  let U : Over S := Over.mk (𝟙 S)
  let : PreconnectedSpace U.left := inferInstanceAs (PreconnectedSpace S)
  let F : ∀ V : Over S, (V ⟶ U) →
      (V ⟶ (splitTorus S I).X) → (V ⟶ (splitTorus S J).X) :=
    fun _ _ t => (t ≫ f.hom.hom) * (t ≫ g.hom.hom)⁻¹
  have hF : HomFamily.IsHomFamily F := by
    constructor
    · intro V a t₁ t₂
      dsimp [F]
      simp only [MonObj.mul_comp, mul_inv_rev]
      ac_rfl
    · intro V W c a t
      dsimp [F]
      simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  let eI := Iso.refl (splitTorus S I)
  let eJ := Iso.refl (splitTorus S J)
  have hz (V : Over S) (x : I → (Γ(V.left, ⊤))ˣ) :
      HomFamily.rectPow (0 : Matrix J I ℤ) x = 1 := by
    funext j
    simp [HomFamily.rectPow]
  have hb : HomFamily.ActsBy eI eJ F 0 (TorusConjugation.overHom (U := U) b) := by
    intro V c x
    have ha : c.left ≫ b = V.hom := by
      have hc := Over.w c
      change c.left ≫ (b ≫ 𝟙 S) = V.hom at hc
      simpa only [Category.comp_id] using hc
    have h := hom_eq_on_factoring_test b hfg V c.left ha
      ((pointsEquiv I V).symm x ≫ eI.inv.hom.hom)
    simp only [HomFamily.famUnits, F, h, mul_inv_cancel, MonObj.one_comp, map_one, hz]
  have hp := (HomFamily.actsBy_overHom_iff eI eJ hF b 0).mp hb
  have hall := HomFamily.actsBy_of_forall_actsAtPoint eI eJ hF 0
    (HomFamily.actsAtPoint_of_preconnected eI eJ hF 0 hp)
  apply hom_ext_points
  intro V t
  let a : V ⟶ U := Over.homMk V.hom (by simp [U])
  have h := hall V a (pointsEquiv I V t)
  simp only [HomFamily.famUnits, eI, eJ, Iso.refl_inv, Iso.refl_hom,
    Grp.id_hom_hom, Category.comp_id, MulEquiv.symm_apply_apply, F, hz] at h
  have he : (t ≫ f.hom.hom) * (t ≫ g.hom.hom)⁻¹ = 1 := by
    apply (pointsEquiv J V).injective
    simpa only [map_one] using h
  exact mul_inv_eq_one.mp he

/-- A field fibre detects the entire hom set of two split tori over a
preconnected base, with their canonical actual base-change maps. -/
theorem baseChange_hom_injective
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    Function.Injective
      (fun f : splitTorus S I ⟶ splitTorus S J => (baseChange b).map f) :=
  fun _ _ h => hom_eq_of_field_baseChange b h

variable [DecidableEq J]

/-- Every actual split-torus homomorphism over a preconnected base is the
integral-coordinate extension of its homomorphism on one field fibre. -/
theorem hom_eq_exponentHom_of_field_baseChange
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (f : splitTorus S I ⟶ splitTorus S J) :
    f = CommGroupScheme.groupHom (exponentHom S I J (fieldFibreCharacterMap b f)) := by
  let c := (baseChangeIso b I).inv ≫ (baseChange b).map f ≫ (baseChangeIso b J).hom
  let χ := characterMap I J c
  have hc : CommGroupScheme.groupHom (exponentHom (Spec (CommRingCat.of k)) I J χ) =
      c := congrArg CommGroupScheme.groupHom (exponentHom_characterMap k I J c)
  have hb := congrArg CommGroupScheme.groupHom (exponentHom_baseChange S I J b χ)
  change (baseChangeIso b I).hom ≫
      CommGroupScheme.groupHom (exponentHom (Spec (CommRingCat.of k)) I J χ) =
    (baseChange b).map (CommGroupScheme.groupHom (exponentHom S I J χ)) ≫
      (baseChangeIso b J).hom at hb
  rw [hc] at hb
  apply hom_eq_of_field_baseChange b
  apply (cancel_mono (baseChangeIso b J).hom).mp
  simpa only [c, χ, fieldFibreCharacterMap, Category.assoc, Iso.hom_inv_id_assoc] using hb

/-- The character action of the field fibre gives the exact character
pullback equation over the whole preconnected base. -/
theorem comp_exponentCharacter_of_field_baseChange
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (f : splitTorus S I ⟶ splitTorus S J) (m : J → ℤ) :
    f ≫ CommGroupScheme.groupHom (exponentCharacter S J m) =
      CommGroupScheme.groupHom (exponentCharacter S I
        (fieldFibreCharacterMap b f m)) := by
  conv_lhs => rw [hom_eq_exponentHom_of_field_baseChange b f]
  exact congrArg CommGroupScheme.groupHom
    (exponentHom_comp_exponentCharacter S I J _ m)

/-- An actual split-torus automorphism over a preconnected scheme is the
integral extension of its actual automorphism on any specified field fibre. -/
theorem iso_eq_fieldAutomorphismExtension
    [DecidableEq I] {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (e : splitTorus S I ≅ splitTorus S I) :
    e = fieldAutomorphismExtension k I S
      ((baseChangeIso b I).symm ≪≫ (baseChange b).mapIso e ≪≫ baseChangeIso b I) := by
  apply Iso.ext
  exact hom_eq_exponentHom_of_field_baseChange b e.hom

end splitTorus

end Langlands.GroupScheme
