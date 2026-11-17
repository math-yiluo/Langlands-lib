import Langlands.GroupScheme.Reductive.SchemeCoordinateRootDatum

/-! # One full root datum over an arbitrary connected base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {S : Scheme.{u}} {I : Type u} [Fintype I]
  {G : GroupScheme S} [IsAffineHom G.X.hom]
  {i : splitTorus S I ⟶ G}

local instance affineFieldPullback (k : Type u) [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- Identity-lattice equivalence transports realization on any supplied
actual field fibre of an arbitrary base scheme. -/
theorem IsRealizedOver.of_identityEquiv
    {J J' : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    {Q : RootDatum J' (I → ℤ) (I → ℤ)}
    {k : Type u} [Field k] {b : Spec (CommRingCat.of k) ⟶ S}
    (hP : IsRealizedOver I G i P k b) (e : RootPairing.Equiv P Q)
    (hw : e.toHom.weightMap = LinearMap.id)
    (hc : e.toHom.coweightMap = LinearMap.id) :
    IsRealizedOver I G i Q k b :=
  isRootDatumOf_of_identityEquiv k hP e hw hc

/-- Two data realized on the same actual field fibre of a supplied split
maximal torus agree with both entire coordinate lattices fixed. -/
theorem IsRealizedOver.exists_identityEquiv
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J J' : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    {Q : RootDatum J' (I → ℤ) (I → ℤ)}
    {k : Type u} [Field k] {b : Spec (CommRingCat.of k) ⟶ S}
    (hP : IsRealizedOver I G i P k b) (hQ : IsRealizedOver I G i Q k b) :
    ∃ e : RootPairing.Equiv P Q,
      e.toHom.weightMap = LinearMap.id ∧ e.toHom.coweightMap = LinearMap.id := by
  let := hG.smooth
  have hm : IsMaximalTorus (T := splitTorus.commGroupScheme _ I)
      ((splitTorus.baseChangeIso b I).inv ≫ (baseChange b).map i) :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
      (T' := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeIso b I).symm (hmax.fieldPoint b)
  exact exists_identityEquiv_of_actualField k I ((baseChange b).obj G)
    (hG.isConnectedReductive_baseChange b) _ hm P Q hP hQ

end CoordinateRootDatum

/-- A finite reduced full datum realized on one actual field fibre of a
supplied split maximal torus is realized on all field fibres over a connected
base scheme. -/
theorem isGlobalCoordinateRootDatumOf_of_connected
    {S : Scheme.{u}} [ConnectedSpace S]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) (hG : IsReductive G)
    (i : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} [Finite J] (P : RootDatum J (I → ℤ) (I → ℤ))
    (hred : P.IsReduced) (k : Type u) [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S)
    (hP : letI := hG.isAffineHom; CoordinateRootDatum.IsRealizedOver I G i P k b) :
    letI := hG.isAffineHom
    CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I G i P := by
  classical
  let := hG.isAffineHom
  let L : Set S := {p | ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
    ∀ (l : Type u) [Field l] (c : Spec (CommRingCat.of l) ⟶ S),
      c (IsLocalRing.closedPoint l) ∈ U →
      CoordinateRootDatum.IsRealizedOver I G i P l c}
  have hopen : IsOpen L := by
    rw [isOpen_iff_forall_mem_open]
    rintro p ⟨U, hU, hpU, hUP⟩
    exact ⟨U, fun q hq => ⟨U, hU, hq, hUP⟩, hU, hpU⟩
  have hnonempty : L.Nonempty := by
    obtain ⟨J', _, Q, U, -, hU, hbU, hUQ⟩ :=
      exists_open_schemeCoordinateRootDatum I G hG i hmax (b (IsLocalRing.closedPoint k))
    obtain ⟨e, hw, hc⟩ := (hUQ k b hbU).exists_identityEquiv hG hmax hP
    refine ⟨b (IsLocalRing.closedPoint k), U, hU, hbU, ?_⟩
    intro l _ c hcU
    exact (hUQ l c hcU).of_identityEquiv e hw hc
  have hcomplement : IsOpen Lᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨J', _, Q, V, -, hV, hpV, hVQ⟩ :=
      exists_open_schemeCoordinateRootDatum I G hG i hmax p
    refine ⟨V, ?_, hV, hpV⟩
    intro q hqV hqL
    obtain ⟨U, -, hqU, hUP⟩ := hqL
    let l := S.residueField q
    let c := S.fromSpecResidueField q
    have hc : c (IsLocalRing.closedPoint l) = q :=
      Scheme.fromSpecResidueField_apply _ _
    obtain ⟨e, hw, hh⟩ := (hVQ l c (hc.symm ▸ hqV)).exists_identityEquiv
      hG hmax (hUP l c (hc.symm ▸ hqU))
    apply hp
    refine ⟨V, hV, hpV, ?_⟩
    intro F _ d hdV
    exact (hVQ F d hdV).of_identityEquiv e hw hh
  have hL : L = Set.univ :=
    (show IsClopen L from ⟨isOpen_compl_iff.mp hcomplement, hopen⟩).eq_univ hnonempty
  refine ⟨inferInstance, hred, ?_⟩
  intro l _ c
  have hcL : c (IsLocalRing.closedPoint l) ∈ L := by rw [hL]; trivial
  obtain ⟨U, -, hcU, hUP⟩ := hcL
  exact hUP l c hcU

/-- A supplied split fibrewise maximal torus in a reductive group over any
connected scheme carries one finite reduced full coordinate root datum on
every actual field-valued fibre. -/
theorem exists_globalCoordinateRootDatumOf_of_connected
    {S : Scheme.{u}} [ConnectedSpace S]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) (hG : IsReductive G)
    (i : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    letI := hG.isAffineHom
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I G i P := by
  classical
  let := hG.isAffineHom
  let s : S := Classical.choice inferInstance
  obtain ⟨J, hJ, P, U, hred, -, hsU, hP⟩ :=
    exists_open_schemeCoordinateRootDatum I G hG i hmax s
  let : Finite J := hJ
  let k := S.residueField s
  let b := S.fromSpecResidueField s
  have hb : b (IsLocalRing.closedPoint k) = s := Scheme.fromSpecResidueField_apply _ _
  exact ⟨J, P, isGlobalCoordinateRootDatumOf_of_connected I G hG i hmax P hred k b
    (hP k b (hb.symm ▸ hsU))⟩


/-- Choose a full finite reduced coordinate root datum over an arbitrary
connected base scheme, with its realization on every actual field fibre. -/
def globalCoordinateRootDatumOfConnected
    {S : Scheme.{u}} [ConnectedSpace S]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme S) (hG : IsReductive G) (i : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i) :
    letI := hG.isAffineHom
    {D : Σ J : Type u, RootDatum J (I → ℤ) (I → ℤ) //
      CoordinateRootDatum.IsGlobalCoordinateRootDatumOf I G i D.2} := by
  let := hG.isAffineHom
  let h := exists_globalCoordinateRootDatumOf_of_connected I G hG i hmax
  exact ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
