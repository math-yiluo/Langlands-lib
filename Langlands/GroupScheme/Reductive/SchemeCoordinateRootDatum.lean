import Langlands.GroupScheme.Reductive.SplitRootDatumNeighbourhood
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.SplitDataTransport
import Langlands.GroupScheme.Reductive.SplitDataBaseChange
import Langlands.GroupScheme.Reductive.RootDatumUniquenessProof
import Mathlib.Topology.Connected.Clopen

/-! # Coordinate root data on an arbitrary base scheme -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

section FieldComparison

/-- Two full coordinate data of the same split maximal torus over a field
admit an equivalence fixing both entire coordinate lattices. -/
theorem exists_identityEquiv_of_actualField
    (k : Type u) [Field k] (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hmax : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J J' : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I → ℤ) (I → ℤ))
    (hP : letI := hG.isAffineHom; IsRootDatumOf i (fieldRealization k P))
    (hQ : letI := hG.isAffineHom; IsRootDatumOf i (fieldRealization k Q)) :
    ∃ e : RootPairing.Equiv P Q,
      e.toHom.weightMap = LinearMap.id ∧ e.toHom.coweightMap = LinearMap.id := by
  let := hG.isAffineHom
  obtain ⟨e, hr, hc⟩ := rootDatumUniqueness k G hG (splitTorus.commGroupScheme _ I)
    (isSplitTorus_splitTorus I) i hmax J J'
    (fieldRealization k P) (fieldRealization k Q) hP hQ
  have hr' (a : J) : Q.root (e a) = P.root a := by
    apply (splitTorus.characterLatticeEquiv k I).symm.injective
    simpa only [Function.comp_apply, fieldRealization_root,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm] using congrFun hr a
  have hc' (a : J) : Q.coroot (e a) = P.coroot a := by
    apply (splitTorus.cocharacterLatticeEquiv k I).symm.injective
    simpa only [Function.comp_apply, fieldRealization_coroot,
      splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm] using congrFun hc a
  have hpq : P.toLinearMap = Q.toLinearMap := by
    ext m n
    exact (pairing_of_isRootDatumOf k P i hP m n).trans
      (pairing_of_isRootDatumOf k Q i hQ m n).symm
  let f : RootPairing.Equiv P Q := {
    weightMap := LinearMap.id
    coweightMap := LinearMap.id
    indexEquiv := e
    weight_coweight_transpose := by
      ext n m
      change Q.toLinearMap m n = P.toLinearMap m n
      rw [hpq]
    root_weightMap := by funext a; exact (hr' a).symm
    coroot_coweightMap := by
      funext a
      simpa only [Function.comp_apply, LinearMap.id_apply, Equiv.apply_symm_apply]
        using hc' (e.symm a)
    bijective_weightMap := Function.bijective_id
    bijective_coweightMap := Function.bijective_id }
  exact ⟨f, rfl, rfl⟩

end FieldComparison

section GeneralBase

variable {S T : Scheme.{u}} (I : Type u) [Fintype I]
  (G : GroupScheme S) [IsAffineHom G.X.hom]
  (i : splitTorus S I ⟶ G) {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))

local instance affinePullback (a : T ⟶ S) :
    IsAffineHom ((baseChange a).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom a inferInstance

/-- A full coordinate datum is realized on the actual fibre at the supplied
field-valued point of an arbitrary base scheme. -/
def IsRealizedOver (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S) : Prop :=
  IsRootDatumOf (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i)
    (fieldRealization k P)

/-- Normalized coordinate realizations agree for direct and successive
pullbacks, retaining the original field-valued point. -/
theorem isRealizedOver_baseChange_iff (a : T ⟶ S)
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ T) :
    IsRealizedOver I ((baseChange a).obj G)
      ((splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map i) P k b ↔
      IsRealizedOver I G i P k (b ≫ a) := by
  unfold IsRealizedOver
  rw [splitTorus.baseChangeTorusHom_comp]
  constructor
  · intro h
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id] using
      h.comp_iso (baseChangeCompIso a b G).symm
  · intro h
    exact h.comp_iso (baseChangeCompIso a b G)

/-- One finite reduced full coordinate datum on an arbitrary base scheme. -/
def IsGlobalCoordinateRootDatumOf : Prop :=
  Finite J ∧ P.IsReduced ∧
    ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      IsRealizedOver I G i P k b

end GeneralBase

end CoordinateRootDatum

/-- A split fibrewise maximal torus in a reductive group over an arbitrary
scheme has a full coordinate root datum on an open neighbourhood of every
base point. -/
theorem exists_open_schemeCoordinateRootDatum
    {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) (hG : IsReductive G)
    (i : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (s : S) :
    letI := hG.isAffineHom
    ∃ (J : Type u) (_ : Finite J) (P : RootDatum J (I → ℤ) (I → ℤ))
      (U : Set S), P.IsReduced ∧ IsOpen U ∧ s ∈ U ∧
      ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
        b (IsLocalRing.closedPoint k) ∈ U →
        CoordinateRootDatum.IsRealizedOver I G i P k b := by
  classical
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨R, a, ha, p, hp⟩ := Scheme.exists_Spec_apply_eq s
  let := ha
  let H := (baseChange a).obj G
  let j : splitTorus (Spec R) I ⟶ H :=
    (splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map i
  have : IsAffineHom H.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom a))
  have hmj : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) j :=
    hmax.baseChange_coordinates a
  obtain ⟨J, hJ, P, U, hred, hU, hpU, -, hP⟩ :=
    exists_open_coordinateRootDatum I H (hG.baseChange a) j hmj p
  let V := a ''ᵁ (⟨U, hU⟩ : (Spec R).Opens)
  refine ⟨J, hJ, P, V, hred, V.isOpen, ?_, ?_⟩
  · exact ⟨p, hpU, hp⟩
  · intro k _ b hb
    obtain ⟨q, hqU, hq⟩ := hb
    change q ∈ U at hqU
    change a q = b (IsLocalRing.closedPoint k) at hq
    have hrange : Set.range b ⊆ Set.range a := by
      rintro _ ⟨z, rfl⟩
      have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact ⟨q, hq.trans (congrArg b hz).symm⟩
    let c := IsOpenImmersion.lift a b hrange
    have hcb : c ≫ a = b := IsOpenImmersion.lift_fac a b hrange
    have hcU : c (IsLocalRing.closedPoint k) ∈ U := by
      have hcq : c (IsLocalRing.closedPoint k) = q := by
        apply a.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hcb]
        exact hq.symm
      simpa only [hcq] using hqU
    let φ := Spec.preimage c
    let : Algebra R k := φ.hom.toAlgebra
    have hφ : algebraBaseMap R k = c := Spec.map_preimage _
    have hlocal : CoordinateRootDatum.IsRealizedOver I H j P k c := by
      rw [← hφ]
      exact hP k (by rw [hφ]; exact hcU)
    have hactual := (CoordinateRootDatum.isRealizedOver_baseChange_iff I G i P a k c).mp hlocal
    rwa [hcb] at hactual


/-- Choose the full coordinate datum supplied by the open-neighbourhood
construction at a point of an arbitrary base scheme. -/
def schemeCoordinateRootDatumAtPoint
    {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) (hG : IsReductive G) (i : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) (s : S) :
    Σ J : Type u, RootDatum J (I → ℤ) (I → ℤ) := by
  let h := exists_open_schemeCoordinateRootDatum I G hG i hmax s
  exact ⟨h.choose, h.choose_spec.choose_spec.choose⟩

end Langlands.GroupScheme
