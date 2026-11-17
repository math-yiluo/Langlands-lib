import Langlands.GroupScheme.Reductive.RegularCocharacterCentralizer
import Langlands.GroupScheme.RelativeLevi.BorelResidueCocharacter
import Langlands.GroupScheme.RelativeLevi.BorelDynamicNeighbourhood
import Langlands.LinearAlgebra.RootDatumCoweightFace
import Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator

/-! # Coordinate root bases adapted to a supplied relative Borel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace splitTorus

/-- On a specified field fibre a cocharacter has the same pullback as one
globally fixed integer exponent vector. The base scheme need not be connected. -/
theorem exists_exponentCocharacter_eq_on_field
    {S : Scheme.{u}} {I : Type u} [Fintype I]
    (ν : cocharacterLattice (commGroupScheme S I))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    ∃ n : I → ℤ,
      cocharacterLattice.baseChange b _ (exponentCocharacter S I n) =
        cocharacterLattice.baseChange b _ ν := by
  let νk := cocharacterLattice.baseChange b _ ν ≫ (commBaseChangeIso b I).hom
  let n := cocharacterLatticeEquiv k I νk
  refine ⟨n, (cancel_mono (commBaseChangeIso b I).hom).mp ?_⟩
  rw [exponentCocharacter_baseChange,
    exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
  exact (cocharacterLatticeEquiv k I).symm_apply_apply νk

end splitTorus

namespace RelativeLevi

/-- A prescribed torus cocharacter presenting a supplied Borel on one residue
fibre presents that same Borel on a neighbourhood, retaining the cocharacter. -/
theorem exists_open_borelPresentation_of_residue
    {S : Scheme.{u}} {G B : GroupScheme S} {T : CommGroupScheme S}
    (t : T.toGrp ⟶ G) (j : B ⟶ G) (hG : IsReductive G)
    (hj : IsRelativeBorelSubgroup j)
    (htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (s : S) (ν : cocharacterLattice T)
    (hpos : SubgroupFunctor.range (residueFiberHom j s) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
        (CommGroupScheme.groupHom ν ≫ t))) :
    ∃ (U : Scheme.{u}) (p : U ⟶ S), IsOpenImmersion p ∧
      s ∈ Set.range p ∧
      SubgroupFunctor.range ((GroupScheme.baseChange p).map j) =
        Dynamic.parabolic (Dynamic.baseChangeCocharacter p
          (CommGroupScheme.groupHom ν ≫ t)) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : GeometricallyConnected G.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ b => (hG.isConnectedReductive_baseChange b).connectedSpace)
  have : Smooth B.X.hom := hj.isRelativeParabolicSubgroup.smooth
  have : IsAffineHom B.X.hom := hj.isRelativeParabolicSubgroup.isAffineHom
  have : GeometricallyConnected B.X.hom :=
    hj.isRelativeParabolicSubgroup.geometricallyConnected hG
  have : Mono j.hom.hom := hj.isRelativeParabolicSubgroup.mono
  have : Mono j.hom.hom.left := Over.mono_left_of_mono _
  have hjr : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  let f := hjr.liftOfLE t htj
  let χB := CommGroupScheme.groupHom ν ≫ f
  have hχ : χB ≫ j = CommGroupScheme.groupHom ν ≫ t := by
    rw [Category.assoc, hjr.liftOfLE_comp]
  let b := S.fromSpecResidueField s
  have hbpoint : b (IsLocalRing.closedPoint (S.residueField s)) = s :=
    Scheme.fromSpecResidueField_apply _ _
  have hjc : IsClosedSubgroup ((GroupScheme.baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint (S.residueField s))))).map j) := by
    rw [hbpoint]
    exact (hj.residueFiber s).1.isClosedSubgroup
  obtain ⟨U, p, hp, bU, hbU, hpres⟩ :=
    Dynamic.exists_local_presentation_of_fieldPoint j χB b hjc
      (by rw [hχ]; exact hpos)
  refine ⟨U, p, hp, ?_, ?_⟩
  · refine ⟨bU (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hbU]
    exact hbpoint
  · rwa [hχ] at hpres

end RelativeLevi

namespace CoordinateRootDatum

variable {I J : Type u} [Fintype I] [Finite J]
  (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced]

/-- A regular coordinate coweight, with the standard pairing, determines
a base whose positive roots are exactly its positive integer pairings. -/
theorem exists_base_of_regularExponent (n : I → ℤ)
    (hpair : ∀ m v, P.toLinearMap m v = ∑ i, m i * v i)
    (hn : ∀ a : J, ∑ i, P.root a i * n i ≠ 0) :
    ∃ b : P.Base, ∀ a, b.IsPos a ↔ 0 < ∑ i, P.root a i * n i := by
  let : Fintype J := Fintype.ofFinite J
  have hf : ∀ a, P.root' a n ≠ 0 := by
    intro a
    change P.toLinearMap (P.root a) n ≠ 0
    rw [hpair]
    exact hn a
  obtain ⟨b, hb⟩ :=
    Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P n hf
  let f := P.flip.toLinearMap n
  have hsimple : ∀ a ∈ b.support, 0 < f (P.root a) := by
    intro a ha
    have ha' : a ∈ IsAddIndecomposable.baseOf P.root (f : (I → ℤ) →+ ℤ) := by
      rw [← hb]
      exact ha
    exact ha'.1
  refine ⟨b, fun a => ?_⟩
  have h := Langlands.LinearAlgebra.isPos_iff_of_pos_simple P b f hsimple a
  change b.IsPos a ↔ 0 < P.toLinearMap (P.root a) n at h
  simpa only [hpair] using h

end CoordinateRootDatum

namespace AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G B : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : B ⟶ G) (P : RootDatum J (I → ℤ) (I → ℤ))
  (hP : IsFibrewiseRootDatumOf I G i P)

include hP in
/-- Centralization by the supplied coordinate torus on one field fibre
forces every root to pair nontrivially with the exponent. -/
theorem regularExponent_of_centralizer_field
    (hi : IsClosedSubgroup i) (n : I → ℤ)
    (k : Type u) [Field k] [Algebra R k]
    (hZ : Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (algebraBaseMap R k) (cocharacter i n)) =
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap R k)).map i))
    (hG : IsReductive G) :
    ∀ a : J, ∑ l, P.root a l * n l ≠ 0 := by
  let ik := splitTorus.baseChangeHom (K := k) G I i
  have hred := hG.isConnectedReductive_algebraMap k
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom :=
    hred.isAffineHom
  have : Smooth ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom :=
    hred.smooth
  have : LocallyOfFiniteType
      ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom := inferInstance
  have hik : IsClosedSubgroup ik :=
    (hi.baseChange (algebraBaseMap R k)).iso_comp
      (splitTorus.baseChangeIso (algebraBaseMap R k) I).symm
  have : IsClosedImmersion ik.hom.hom.left := hik
  have : Mono ik.hom.hom := Over.mono_of_mono_left _
  have hz : (Dynamic.centralizer
      (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) ≫ ik)).IsRepresentedBy
      ik := by
    refine ⟨inferInstance, ?_⟩
    rw [cocharacter_baseChange] at hZ
    exact (SubgroupFunctor.range_iso_comp
      (splitTorus.baseChangeIso (algebraBaseMap R k) I).symm _).trans hZ.symm
  have hreg := isRegularCocharacter_of_centralizer_isRepresentedBy_torus
    (G := (GroupScheme.baseChange (algebraBaseMap R k)).obj G)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (isSplitTorus_splitTorus I) ik
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) hz
  intro a
  have hroot := (hP.mem_roots_iff k (P.root a)).mpr ⟨a, rfl⟩
  have h := hreg _ hroot
  rwa [splitTorus.latticePairing_exponentCharacter_exponentCocharacter] at h

include hP in
/-- Near each base point the supplied Borel is presented by a fixed regular
coordinate exponent, with a root base adapted to its sign. Its global
centralizer is the original coordinate torus. -/
theorem exists_base_adapted_to_suppliedBorel
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hj : IsRelativeBorelSubgroup j)
    (htj : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (s : Spec (CommRingCat.of R)) :
    ∃ (n : I → ℤ) (b : P.Base),
      (∀ a : J, ∑ l, P.root a l * n l ≠ 0) ∧
      (∀ a : J, b.IsPos a ↔ 0 < ∑ l, P.root a l * n l) ∧
      Dynamic.centralizer (cocharacter i n) = SubgroupFunctor.range i ∧
      ∃ (U : Scheme.{u}) (p : U ⟶ Spec (CommRingCat.of R)),
        IsOpenImmersion p ∧ s ∈ Set.range p ∧
        SubgroupFunctor.range ((GroupScheme.baseChange p).map j) =
          Dynamic.parabolic (Dynamic.baseChangeCocharacter p (cocharacter i n)) := by
  let S := Spec (CommRingCat.of R)
  let T := splitTorus.commGroupScheme S I
  let f := S.fromSpecResidueField s
  let k := S.residueField s
  obtain ⟨ν, hpos, hcent⟩ :=
    exists_residueBorelCocharacter (T := T) hG
      (isSplitTorus_splitTorus I) i hmax j hj htj s
  obtain ⟨n, hnν⟩ := splitTorus.exists_exponentCocharacter_eq_on_field ν f
  have he : Dynamic.baseChangeCocharacter f
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter S I n)) =
      Dynamic.baseChangeCocharacter f (CommGroupScheme.groupHom ν) :=
    congrArg CommGroupScheme.groupHom hnν
  have hχ : Dynamic.baseChangeCocharacter f (cocharacter i n) =
      Dynamic.baseChangeCocharacter f (CommGroupScheme.groupHom ν ≫ i) := by
    rw [cocharacter, Dynamic.baseChangeCocharacter_comp,
      Dynamic.baseChangeCocharacter_comp]
    exact congrArg (fun v => v ≫ (GroupScheme.baseChange f).map i) he
  have hposn : SubgroupFunctor.range (RelativeLevi.residueFiberHom j s) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter f (cocharacter i n)) := by
    rw [hχ]
    exact hpos
  have hcentn : Dynamic.centralizer
      (Dynamic.baseChangeCocharacter f (cocharacter i n)) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) := by
    rw [hχ]
    exact hcent
  let φ := Spec.preimage f
  let : Algebra R k := φ.hom.toAlgebra
  have hf : algebraBaseMap R k = f := Spec.map_preimage _
  have hn : ∀ a : J, ∑ l, P.root a l * n l ≠ 0 :=
    regularExponent_of_centralizer_field i P hP hi n k (by rw [hf]; exact hcentn) hG
  have : Finite J := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b, hb⟩ := CoordinateRootDatum.exists_base_of_regularExponent P n
    (hP.pairing k) hn
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  refine ⟨n, b, hn, hb, centralizer_eq_range_of_mono i n P hP hn hG hmax, ?_⟩
  exact RelativeLevi.exists_open_borelPresentation_of_residue (T := T) i j hG hj htj s
    (splitTorus.exponentCocharacter S I n) hposn

/-- Actual local chamber data for the supplied Borel and coordinate torus,
including a neighbourhood on which the chosen exponent presents that Borel. -/
structure AdaptedBorelRootBaseData (s : Spec (CommRingCat.of R)) where
  exponent : I → ℤ
  rootBase : P.Base
  regular : ∀ a : J, ∑ l, P.root a l * exponent l ≠ 0
  positive_iff : ∀ a : J, rootBase.IsPos a ↔ 0 < ∑ l, P.root a l * exponent l
  centralizer_eq : Dynamic.centralizer (cocharacter i exponent) = SubgroupFunctor.range i
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ Spec (CommRingCat.of R)
  openImmersion : IsOpenImmersion projection
  contains : s ∈ Set.range projection
  presentation : SubgroupFunctor.range ((GroupScheme.baseChange projection).map j) =
    Dynamic.parabolic (Dynamic.baseChangeCocharacter projection (cocharacter i exponent))

/-- Choose the local chamber data constructed from the actual supplied Borel. -/
def adaptedBorelRootBase
    (hG : IsReductive G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hj : IsRelativeBorelSubgroup j)
    (htj : SubgroupFunctor.range i ≤ SubgroupFunctor.range j)
    (s : Spec (CommRingCat.of R)) : AdaptedBorelRootBaseData i j P s :=
  Classical.choice (show Nonempty (AdaptedBorelRootBaseData i j P s) from by
    obtain ⟨n, b, hn, hb, hcent, U, p, hp, hs, hpres⟩ :=
      exists_base_adapted_to_suppliedBorel i j P hP hG hi hmax hj htj s
    exact ⟨⟨n, b, hn, hb, hcent, U, p, hp, hs, hpres⟩⟩)

end AffineRegularBorel

end Langlands.GroupScheme
