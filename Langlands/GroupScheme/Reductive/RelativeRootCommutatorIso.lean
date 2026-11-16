import Langlands.GroupScheme.Reductive.RelativeRootCommutatorMap
import Langlands.GroupScheme.Reductive.RelativeRootGroupFibre
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.AlgebraicGeometry.DiscreteValuationFibreIsomorphism

/-! # Invertibility of actual root commutator maps -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.LocalRootGroup
open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu a : I → ℤ)
  (K : Type u) [Field K] [Algebra R K]
  (Φ : Ga K ≅ UK i mu nu K)
  (hΦ : IsRootParametrization (splitTorus.baseChangeHom (K := K) G I i) a
    (fibreRootMap i mu nu K Φ))
  (t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
    (splitTorus (Spec (CommRingCat.of R)) I).X)

include hΦ in
theorem rootCommutatorMap_fibre_scalar
    (Z : Over (Spec (CommRingCat.of K))) (c : Γ(Z.left, ⊤)) :
    (VectorGroup.scalarPoint _ Z c ≫ Φ.hom.hom.hom) ≫
        (Over.pullback (algebraBaseMap R K)).map (rootCommutatorMap i mu nu t) =
      VectorGroup.scalarPoint _ Z
        (((show Γ(Z.left, ⊤) from VectorGroup.charValue (splitTorus.exponentCharacter _ I a)
          ((Over.map (algebraBaseMap R K)).obj Z)
          ((splitTorus _ I).constantPoint t ((Over.map (algebraBaseMap R K)).obj Z))) - 1) * c) ≫
        Φ.hom.hom.hom := by
  let b := algebraBaseMap R K
  let j := (GroupScheme.baseChange b).map (incl i mu nu)
  have hm : Mono (fibreRootMap i mu nu K Φ).hom.hom := hΦ.represents.1
  have hm' : Mono (Φ.hom.hom.hom ≫ j.hom.hom) := by
    simpa only [fibreRootMap_eq, Grp.comp_hom_hom] using hm
  have : Mono j.hom.hom := (mono_comp_iff_of_isIso _ _).mp hm'
  apply (cancel_mono j.hom.hom).1
  let q := ((GroupScheme.baseChange b).obj (splitTorus _ I)).constantPoint
    (baseChangeBasePoint b (splitTorus _ I) t) Z
  let s := q ≫ (splitTorus.baseChangeIso b I).hom.hom.hom
  have hs : s ≫ (splitTorus.baseChangeHom (K := K) G I i).hom.hom =
      q ≫ ((GroupScheme.baseChange b).map i).hom.hom := by
    change q ≫ (splitTorus.baseChangeIso b I).hom.hom.hom ≫
      (splitTorus.baseChangeIso b I).inv.hom.hom ≫
        ((GroupScheme.baseChange b).map i).hom.hom = _
    rw [← Category.assoc (splitTorus.baseChangeIso b I).hom.hom.hom,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.id_comp]
  have hv : VectorGroup.charValue (splitTorus.exponentCharacter _ I a) Z s =
      VectorGroup.charValue (splitTorus.exponentCharacter _ I a)
        ((Over.map b).obj Z) ((splitTorus _ I).constantPoint t ((Over.map b).obj Z)) := by
    rw [LocalSplitRootBaseChange.charValue_exponentCharacter_baseChange (R := R) K]
    dsimp only [s]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id, baseChangePointsEquiv_constantPoint]
  have heq := hΦ.equivariant Z s c
  rw [hs, hv, fibreRootMap_eq] at heq
  simp only [rootPoint, Grp.comp_hom_hom] at heq
  refine (AutomorphicAction.commutatorMap_baseChange_comp
    (UnipotentTorus.action (torusZ i mu) nu) t i (incl i mu nu)
    (fun _ => action_act_comp_incl i mu nu) b
    (VectorGroup.scalarPoint _ Z c ≫ Φ.hom.hom.hom)).trans ?_
  simp only [Category.assoc] at heq ⊢
  rw [heq]
  let v : Γ(Z.left, ⊤) := VectorGroup.charValue (splitTorus.exponentCharacter _ I a)
    ((Over.map b).obj Z) ((splitTorus _ I).constantPoint t ((Over.map b).obj Z))
  have hroot : rootPoint (fibreRootMap i mu nu K Φ) Z (v * c) *
      (rootPoint (fibreRootMap i mu nu K Φ) Z c)⁻¹ =
      rootPoint (fibreRootMap i mu nu K Φ) Z ((v - 1) * c) := by
    rw [← rootPoint_neg, ← rootPoint_add]
    congr 1
    ring
  simpa only [rootPoint, fibreRootMap_eq, Grp.comp_hom_hom, Category.assoc] using hroot

include hΦ in
/-- A unit root-character difference makes the commutator map invertible on
this field fibre. -/
theorem isIso_rootCommutatorMap_field
    (hu : IsUnit ((show Γ(Spec (CommRingCat.of R), ⊤) from
      VectorGroup.charValue (splitTorus.exponentCharacter _ I a) (Over.mk (𝟙 _)) t) - 1)) :
    IsIso ((Over.pullback (algebraBaseMap R K)).map (rootCommutatorMap i mu nu t)) := by
  apply isIso_of_scalar_points _ Φ
    (fun Z => (show Γ(Z.left, ⊤) from VectorGroup.charValue
      (splitTorus.exponentCharacter _ I a) ((Over.map (algebraBaseMap R K)).obj Z)
      ((splitTorus _ I).constantPoint t ((Over.map (algebraBaseMap R K)).obj Z))) - 1)
  · intro Z
    have h := hu.map ((Over.map (algebraBaseMap R K)).obj Z).hom.appTop.hom
    rw [constantPoint, VectorGroup.charValue_comp]
    simp only [map_sub, map_one] at h
    convert h using 1 <;> rfl
  · exact rootCommutatorMap_fibre_scalar i mu nu a K Φ hΦ t

variable {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The actual root commutator map is an isomorphism over an arbitrary ring
when its root-character difference is a unit. -/
theorem isIso_rootCommutatorMap (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (hu : IsUnit ((show Γ(Spec (CommRingCat.of R), ⊤) from
      VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root α))
        (Over.mk (𝟙 _)) t) - 1)) :
    IsIso (rootCommutatorMap i mu (P.coroot α) t) := by
  have := hG.smooth
  have := smooth_Uc i mu (P.coroot α)
  apply Langlands.AlgebraicGeometry.isIso_of_residueField_fibres
  intro s
  let K := (Spec (CommRingCat.of R)).residueField s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R K := φ.hom.toAlgebra
  obtain ⟨Φ, hΦ⟩ := exists_rootFibreParametrization i mu K hG hmax hP α hmu0 hmu
  have h := isIso_rootCommutatorMap_field i mu (P.coroot α) (P.root α) K Φ hΦ t hu
  rwa [show algebraBaseMap R K =
      (Spec (CommRingCat.of R)).fromSpecResidueField s from Spec.map_preimage _] at h

/-- The root commutator isomorphism with its actual scheme map. -/
def rootCommutatorIso (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α)
    (hu : IsUnit ((show Γ(Spec (CommRingCat.of R), ⊤) from
      VectorGroup.charValue (splitTorus.exponentCharacter _ I (P.root α))
        (Over.mk (𝟙 _)) t) - 1)) :
    (Uc i mu (P.coroot α)).X ≅ (Uc i mu (P.coroot α)).X := by
  letI := isIso_rootCommutatorMap i mu t hG hmax hP α hmu0 hmu hu
  exact asIso (rootCommutatorMap i mu (P.coroot α) t)

end Langlands.GroupScheme.LocalRootGroup
