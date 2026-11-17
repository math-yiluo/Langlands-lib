import Langlands.GroupScheme.Reductive.SplitRootDatumNeighbourhood
import Mathlib.Topology.Connected.Clopen

/-! # One full root datum over a connected affine base -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {R : Type u} [CommRing R]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

/-- Two full coordinate data realized on one closed torus fibre admit
an equivalence fixing both entire coordinate lattices. -/
theorem exists_identityEquiv_of_commonField
    (k : Type u) [Field k] [Algebra R k]
    (hclosed : IsClosedSubgroup (splitTorus.baseChangeHom (K := k) G I i))
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    {J' : Type w} (Q : RootDatum J' (I → ℤ) (I → ℤ))
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k P))
    (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k Q)) :
    ∃ e : RootPairing.Equiv P Q,
      e.toHom.weightMap = LinearMap.id ∧ e.toHom.coweightMap = LinearMap.id := by
  let e := Langlands.LinearAlgebra.rootDatumEquivOfFiniteOrderReflections P Q
    (pairing_eq_of_fields I G i k P k Q hP hQ)
    (rootRange_eq_of_weightRanks I G i k P k Q hP hQ (fun _ => rfl))
    (fun a b _ => LocalSplitCorootTransport.isOfFinOrder_mul_of_isRealizedAt
      I G i k hclosed
      (LocalSplitCorootTransport.isRealizedAt_reflection I G i k P hP a)
      (LocalSplitCorootTransport.isRealizedAt_reflection I G i k Q hQ b))
  exact ⟨e, rfl, rfl⟩

end CoordinateRootDatum

/-- A finite reduced full coordinate datum realized on one field fibre of a
reductive group with a split fibrewise maximal torus is realized on every
field fibre when the affine base is connected. -/
theorem isFibrewiseRootDatumOf_of_connected
    {R : Type u} [CommRing R] [ConnectedSpace (Spec (CommRingCat.of R))]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (k : Type u) [Field k] [Algebra R k]
    {J : Type v} [Finite J] (P : RootDatum J (I → ℤ) (I → ℤ))
    (hred : P.IsReduced)
    (hP : letI := hG.isAffineHom
      IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
        (CoordinateRootDatum.fieldRealization k P)) :
    let := hG.isAffineHom
    IsFibrewiseRootDatumOf I G i P := by
  classical
  let := hG.isAffineHom
  let := hG.smooth
  have hclosed (l : Type u) [Field l] [Algebra R l] :=
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax l).2.1
  have hfield (l : Type u) [Field l] [Algebra R l] :
      ∃ (J' : Type u) (Q : RootDatum J' (I → ℤ) (I → ℤ)),
        IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
          (CoordinateRootDatum.fieldRealization l Q) := by
    obtain ⟨J', _, Q, hQ, -⟩ := rootDatumExistence l _
      (hG.isConnectedReductive_algebraMap l)
      (splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)
      (isSplitTorus_splitTorus I) _
      (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax l)
    exact ⟨J', CoordinateRootDatum.ofField l Q,
      CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hQ⟩
  let L : Set (Spec (CommRingCat.of R)) := {p | ∃ U : Set (Spec (CommRingCat.of R)),
    IsOpen U ∧ p ∈ U ∧ ∀ (l : Type u) [Field l] [Algebra R l],
      (algebraBaseMap R l) (IsLocalRing.closedPoint l) ∈ U →
      IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
        (CoordinateRootDatum.fieldRealization l P)}
  have hopen : IsOpen L := by
    rw [isOpen_iff_forall_mem_open]
    rintro p ⟨U, hU, hp, hUP⟩
    exact ⟨U, fun q hq => ⟨U, hU, hq, hUP⟩, hU, hp⟩
  have hcomplement : IsOpen Lᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨J', hJ', Q, V, -, hV, hpV, -, hVQ⟩ :=
      exists_open_coordinateRootDatum I G hG i hmax p
    refine ⟨V, ?_, hV, hpV⟩
    intro q hqV hqL
    obtain ⟨U, hU, hqU, hUP⟩ := hqL
    let l := (Spec (CommRingCat.of R)).residueField q
    let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField q)
    let : Algebra R l := φ.hom.toAlgebra
    have hb : algebraBaseMap R l = (Spec (CommRingCat.of R)).fromSpecResidueField q :=
      Spec.map_preimage _
    have hq : (algebraBaseMap R l) (IsLocalRing.closedPoint l) = q := by
      rw [hb]
      exact Scheme.fromSpecResidueField_apply _ _
    obtain ⟨e, hw, hc⟩ := CoordinateRootDatum.exists_identityEquiv_of_commonField
      I G i l (hclosed l) Q P
      (hVQ l (by rw [hq]; exact hqV)) (hUP l (by rw [hq]; exact hqU))
    apply hp
    refine ⟨V, hV, hpV, ?_⟩
    intro F _ _ hF
    exact CoordinateRootDatum.isRootDatumOf_of_identityEquiv F (hVQ F hF) e hw hc
  have hnonempty : L.Nonempty := by
    obtain ⟨U, hU, hkU, hUP⟩ :=
      LocalSplitCorootTransport.exists_open_isRootDatumOf I G i
        (fun l _ _ => hclosed l) k P hP
    refine ⟨(algebraBaseMap R k) (IsLocalRing.closedPoint k), U, hU, hkU, ?_⟩
    intro l _ _ hl
    obtain ⟨J', Q, hQ⟩ := hfield l
    exact hUP l hl Q hQ
  have hL : L = Set.univ := (show IsClopen L from ⟨isOpen_compl_iff.mp hcomplement, hopen⟩).eq_univ hnonempty
  refine ⟨inferInstance, hred, ?_⟩
  intro l _ _
  have hl : (algebraBaseMap R l) (IsLocalRing.closedPoint l) ∈ L := by rw [hL]; trivial
  obtain ⟨U, -, hlU, hUP⟩ := hl
  exact hUP l hlU

/-- A split fibrewise maximal torus of a reductive group over a connected
affine base carries a single finite reduced full coordinate root datum. -/
theorem exists_fibrewiseRootDatumOf_of_connected
    {R : Type u} [CommRing R] [ConnectedSpace (Spec (CommRingCat.of R))]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    let := hG.isAffineHom
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P := by
  classical
  let := hG.isAffineHom
  let p : Spec (CommRingCat.of R) := Classical.choice inferInstance
  obtain ⟨J, hJ, P, U, hred, -, hpU, -, hP⟩ :=
    exists_open_coordinateRootDatum I G hG i hmax p
  let : Finite J := hJ
  let k := (Spec (CommRingCat.of R)).residueField p
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField p)
  let : Algebra R k := φ.hom.toAlgebra
  have hb : algebraBaseMap R k = (Spec (CommRingCat.of R)).fromSpecResidueField p :=
    Spec.map_preimage _
  have hp : (algebraBaseMap R k) (IsLocalRing.closedPoint k) = p := by
    rw [hb]
    exact Scheme.fromSpecResidueField_apply _ _
  exact ⟨J, P, isFibrewiseRootDatumOf_of_connected I G hG i hmax k P hred
    (hP k (by rw [hp]; exact hpU))⟩


/-- Choose a full finite reduced coordinate root datum on a connected affine
base, together with its realization on every actual field fibre. -/
def connectedCoordinateRootDatum
    {R : Type u} [CommRing R] [ConnectedSpace (Spec (CommRingCat.of R))]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    letI := hG.isAffineHom
    {D : Σ J : Type u, RootDatum J (I → ℤ) (I → ℤ) //
      IsFibrewiseRootDatumOf I G i D.2} := by
  let := hG.isAffineHom
  let h := exists_fibrewiseRootDatumOf_of_connected I G hG i hmax
  exact ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
