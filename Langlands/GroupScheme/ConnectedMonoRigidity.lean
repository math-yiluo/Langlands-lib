import Langlands.GroupScheme.SmoothIsomorphismLocus
import Mathlib.Topology.Connected.Clopen

/-! # Rigidity of smooth connected group monomorphisms over a connected base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SmoothIsomorphismLocus

local instance rigiditySmoothPullback {S T : Scheme.{u}} (a : T ⟶ S)
    (G : GroupScheme S) [Smooth G.X.hom] :
    Smooth ((baseChange a).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom a))

local instance rigidityAffinePullback {S T : Scheme.{u}} (a : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((baseChange a).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom a inferInstance

local instance rigidityConnectedPullback {S T : Scheme.{u}} (a : T ⟶ S)
    (G : GroupScheme S) [GeometricallyConnected G.X.hom] :
    GeometricallyConnected ((baseChange a).obj G).X.hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom a))

local instance rigidityMonoPullback {S T : Scheme.{u}} (a : T ⟶ S)
    {H G : GroupScheme S} (f : H ⟶ G) [Mono f.hom.hom] :
    Mono ((baseChange a).map f).hom.hom :=
  inferInstanceAs (Mono ((Over.pullback a).map f.hom.hom))

section General

variable {S : Scheme.{u}} {H G : GroupScheme S}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
  (f : H ⟶ G) [Mono f.hom.hom]

/-- The existing open isomorphism locus detects invertibility on any
supplied field fibre of a smooth monomorphism of connected affine families. -/
theorem isIso_field_iff_mem_opens
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsIso ((baseChange b).map f) ↔
      b (IsLocalRing.closedPoint k) ∈ TorusIsomorphismLocus.opens f := by
  constructor
  · intro hb
    obtain ⟨V, q, hq, c, hc, hqf⟩ := exists_open f k b hb
    let := hq
    let := hqf
    have hU := TorusIsomorphismLocus.isIso_opensRange f q
    apply (show q.opensRange ≤ TorusIsomorphismLocus.opens f from
      le_iSup (fun U : {U : S.Opens // IsIso ((baseChange U.ι).map f)} => U.1)
        ⟨q.opensRange, hU⟩)
    change b (IsLocalRing.closedPoint k) ∈ Set.range q
    refine ⟨c (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun z : Spec (CommRingCat.of k) ⟶ S =>
      z (IsLocalRing.closedPoint k)) hc
  · intro hb
    apply TorusIsomorphismLocus.isIso_of_range_subset_opens f b
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst z
    exact hb

/-- On every affine chart, the isomorphism locus is exactly equality of the
locally constant relative Lie ranks. -/
theorem preimage_opens_eq_lieRanks {R : CommRingCat.{u}} (a : Spec R ⟶ S) :
    a ⁻¹' (TorusIsomorphismLocus.opens f : Set S) =
      {p : Spec R | Module.rankAtStalk (R := R)
        (Additive (lieKernel ((baseChange a).obj H) R)) p =
        Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj G) R)) p} := by
  ext p
  let k := (Spec R).residueField p
  let b := (Spec R).fromSpecResidueField p
  have hb : b (IsLocalRing.closedPoint k) = p := Scheme.fromSpecResidueField_apply _ _
  have hc : (b ≫ a) (IsLocalRing.closedPoint k) = a p := by
    change a (b (IsLocalRing.closedPoint k)) = a p
    exact congrArg a hb
  change a p ∈ TorusIsomorphismLocus.opens f ↔ _
  have hmem : a p ∈ TorusIsomorphismLocus.opens f ↔
      IsIso ((baseChange (b ≫ a)).map f) :=
    hc ▸ (isIso_field_iff_mem_opens f k (b ≫ a)).symm
  rw [hmem, TorusIsomorphismLocus.isIso_comp_baseChange_iff]
  have hHc : ConnectedSpace ((baseChange b).obj ((baseChange a).obj H)).X.left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace
        (f := ((baseChange a).obj H).X.hom)) _ _
  have hGc : ConnectedSpace ((baseChange b).obj ((baseChange a).obj G)).X.left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace
        (f := ((baseChange a).obj G).X.hom)) _ _
  have hdH : Lie.dimension ((baseChange b).obj ((baseChange a).obj H)) =
      Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj H) R)) p :=
    (dimension_fieldPoint ((baseChange a).obj H) k b).trans
      (congrArg (Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj H) R))) hb)
  have hdG : Lie.dimension ((baseChange b).obj ((baseChange a).obj G)) =
      Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj G) R)) p :=
    (dimension_fieldPoint ((baseChange a).obj G) k b).trans
      (congrArg (Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj G) R))) hb)
  constructor
  · intro h
    let := h
    exact hdH.symm.trans ((Lie.dimension_eq_of_iso
      (asIso ((baseChange b).map ((baseChange a).map f)))).trans hdG)
  · intro h
    exact Lie.isIso_of_mono_of_dimension_eq _ (hdH.trans (h.trans hdG.symm))

/-- The base isomorphism locus of a smooth monomorphism of geometrically
connected affine group families is clopen. -/
theorem isClopen_opens : IsClopen (TorusIsomorphismLocus.opens f : Set S) := by
  refine ⟨isOpen_compl_iff.mp ?_, (TorusIsomorphismLocus.opens f).isOpen⟩
  rw [isOpen_iff_forall_mem_open]
  intro s hs
  obtain ⟨R, a, ha, p, hp⟩ := Scheme.exists_Spec_apply_eq s
  let := ha
  have hloc : IsLocallyConstant (fun q : Spec R =>
      (Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj H) R)) q,
       Module.rankAtStalk (R := R) (Additive (lieKernel ((baseChange a).obj G) R)) q)) :=
    (Lie.isLocallyConstant_lieRank ((baseChange a).obj H)).prodMk
      (Lie.isLocallyConstant_lieRank ((baseChange a).obj G))
  have hpre : IsOpen (a ⁻¹' (TorusIsomorphismLocus.opens f : Set S)ᶜ) := by
    rw [Set.preimage_compl, preimage_opens_eq_lieRanks]
    exact hloc {z : ℕ × ℕ | z.1 ≠ z.2}
  refine ⟨a '' (a ⁻¹' (TorusIsomorphismLocus.opens f : Set S)ᶜ), ?_,
    a.isOpenMap _ hpre, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hq
  · refine ⟨p, ?_, hp⟩
    change a p ∉ TorusIsomorphismLocus.opens f
    exact hp.symm ▸ hs

/-- Over a connected base, one isomorphic field fibre makes a smooth monic
homomorphism of geometrically connected affine group families an isomorphism. -/
theorem isIso_of_fieldIso_of_connected [ConnectedSpace S]
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : IsIso ((baseChange b).map f)) : IsIso f := by
  have hU : (TorusIsomorphismLocus.opens f : Set S) = Set.univ :=
    (isClopen_opens f).eq_univ
      ⟨b (IsLocalRing.closedPoint k), (isIso_field_iff_mem_opens f k b).mp hb⟩
  have : IsIso ((baseChange (𝟙 S)).map f) :=
    TorusIsomorphismLocus.isIso_of_range_subset_opens f (𝟙 S) (by rw [hU]; exact Set.subset_univ _)
  exact isIso_of_baseChange (𝟙 S) f

/-- The concrete isomorphism obtained from one isomorphic field fibre over a
connected base. Its forward map is the original monomorphism. -/
def isoOfFieldIsoOfConnected [ConnectedSpace S]
    (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : IsIso ((baseChange b).map f)) : H ≅ G := by
  let := isIso_of_fieldIso_of_connected f k b hb
  exact asIso f

end General

end Langlands.GroupScheme.SmoothIsomorphismLocus
