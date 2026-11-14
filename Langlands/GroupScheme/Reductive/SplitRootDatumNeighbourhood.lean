import Langlands.GroupScheme.Reductive.LocalSplitCorootTransport
import Langlands.GroupScheme.Torus.GeometricAdjointWeightRanks
import Langlands.AlgebraicGeometry.FlatClosedPointGeneralization
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof

/-! # Open neighbourhoods preserving a full coordinate root datum -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace LocalSplitCorootTransport

open PointwiseSchemeAction

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual transporter of the coordinate twist by `C`. -/
abbrev coordinateTransporter : Over (Spec (CommRingCat.of R)) :=
  relativeTransporterScheme
    ((Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))).hom ≫
      (splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i)
    ((Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))).hom ≫ i)

/-- The image of the actual coordinate transporter in the base. -/
def realizationLocus : Set (Spec (CommRingCat.of R)) :=
  Set.range (coordinateTransporter I G i C).hom

/-- The image of the smooth coordinate transporter is open. -/
theorem isOpen_realizationLocus [Smooth G.X.hom] :
    IsOpen (realizationLocus I G i C) := by
  have : Smooth (coordinateTransporter I G i C).hom :=
    smooth_relativeTransporterScheme _ _ inferInstance
  exact (coordinateTransporter I G i C).hom.isOpenMap.isOpen_range

/-- An actual realization puts the image of the supplied field point in
the coordinate-transporter image. -/
theorem mem_realizationLocus_of_isRealizedAt
    (k : Type u) [Field k] [Algebra R k] (h : IsRealizedAt I G i C k) :
    (algebraBaseMap R k) (IsLocalRing.closedPoint k) ∈ realizationLocus I G i C := by
  let d := Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))
  obtain ⟨g, hg⟩ := h
  let A := CommAlgCat.of (CommRingCat.of R) k
  let c : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶
      Over.mk (algebraBaseMap R k) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; rfl)
  obtain ⟨y, -⟩ := (exists_relativeTransporter_factor_iff
    (d.hom ≫ (splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i)
    (d.hom ≫ i) (c ≫ g)).mpr
      ((isTransporter_precomp_iso_iff d).mpr (hg.restrict c))
  refine ⟨y.left (IsLocalRing.closedPoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w y]
  rfl

/-- A field point in the coordinate-transporter image admits a realization
after a field extension, with the original base algebra structure retained. -/
theorem exists_extension_of_mem_realizationLocus
    (l : Type u) [Field l] [Algebra R l]
    (h : (algebraBaseMap R l) (IsLocalRing.closedPoint l) ∈ realizationLocus I G i C) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra R L) (_ : Algebra l L)
      (_ : IsScalarTower R l L), IsRealizedAt I G i C L := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (coordinateTransporter I G i C).hom) (g := algebraBaseMap R l)
    x (IsLocalRing.closedPoint l) hx
  let P := Langlands.AlgebraicGeometry.FieldPointLift.ofPullbackPoint w
  let _ : Algebra R P.L := ((algebraMap l P.L).comp (algebraMap R l)).toAlgebra
  have : IsScalarTower R l P.L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨P.L, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  let z : Over.mk (algebraBaseMap R P.L) ⟶ coordinateTransporter I G i C :=
    Over.homMk P.point (by
      change P.point ≫ (coordinateTransporter I G i C).hom =
        Spec.map (CommRingCat.ofHom (algebraMap R P.L))
      rw [P.comm, ← Spec.map_comp]
      rfl)
  let d := Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))
  exact ⟨z ≫ relativeTransporterHom _ _,
    (isTransporter_precomp_iso_iff d).mp
      ((relativeTransporterHom_isTransporter _ _).restrict z)⟩

end LocalSplitCorootTransport

namespace CoordinateRootDatum

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

local instance {k : Type u} [Field k] [Algebra R k] :
    Smooth ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom (algebraBaseMap R k)))

/-- Equal actual weight ranks at two field points identify the root ranges
of their realized coordinate data over an arbitrary base ring. -/
theorem rootRange_eq_of_weightRanks
    (k : Type u) [Field k] [Algebra R k]
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (l : Type u) [Field l] [Algebra R l]
    {J' : Type w} (Q : RootDatum J' (I → ℤ) (I → ℤ))
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k P))
    (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
      (fieldRealization l Q))
    (hrank : ∀ m, splitTorus.exponentWeightRank I G i m
        ((algebraBaseMap R k) (IsLocalRing.closedPoint k)) =
      splitTorus.exponentWeightRank I G i m
        ((algebraBaseMap R l) (IsLocalRing.closedPoint l))) :
    Set.range P.root = Set.range Q.root := by
  ext m
  rw [mem_rootRange_iff k P _ hP, mem_rootRange_iff l Q _ hQ,
    mem_roots_iff_finrank_ne_zero, mem_roots_iff_finrank_ne_zero,
    ← splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter,
    ← splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter,
    splitTorus.finrank_exponentWeightSpace_fieldBaseChange,
    splitTorus.finrank_exponentWeightSpace_fieldBaseChange, hrank,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  simp only [ne_eq, AddEquiv.map_eq_zero_iff]

end CoordinateRootDatum

namespace LocalSplitCorootTransport

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

local instance {k : Type u} [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

/-- A finite coordinate datum realized over one field agrees with every
actual coordinate datum sufficiently near that field point. Smooth
transporter images control the coroots as well as the roots. -/
theorem exists_open_isRootDatumOf
    (hclosed : ∀ (l : Type u) [Field l] [Algebra R l],
      IsClosedSubgroup (splitTorus.baseChangeHom (K := l) G I i))
    (k : Type u) [Field k] [Algebra R k]
    {J : Type v} [Finite J] (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (CoordinateRootDatum.fieldRealization k P)) :
    ∃ U : Set (Spec (CommRingCat.of R)), IsOpen U ∧
      (algebraBaseMap R k) (IsLocalRing.closedPoint k) ∈ U ∧
      ∀ (l : Type u) [Field l] [Algebra R l],
        (algebraBaseMap R l) (IsLocalRing.closedPoint l) ∈ U →
        ∀ {J' : Type w} (Q : RootDatum J' (I → ℤ) (I → ℤ)),
          IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
            (CoordinateRootDatum.fieldRealization l Q) →
          IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
            (CoordinateRootDatum.fieldRealization l P) := by
  classical
  obtain ⟨V, hV, hkV, hrank⟩ := splitTorus.exists_open_exponentWeightRanks_eq
    I G i ((algebraBaseMap R k) (IsLocalRing.closedPoint k))
  let U := V ∩ ⋂ j : J, realizationLocus I G i (P.reflection j)
  refine ⟨U, hV.inter (isOpen_iInter_of_finite (fun j =>
    isOpen_realizationLocus I G i (P.reflection j))), ⟨hkV, ?_⟩, ?_⟩
  · exact Set.mem_iInter.mpr (fun j =>
      mem_realizationLocus_of_isRealizedAt I G i _ k
        (isRealizedAt_reflection I G i k P hP j))
  · intro l _ _ hl J' Q hQ
    have horder : ∀ (j' : J') (j : J), Q.root j' = P.root j →
        IsOfFinOrder (Q.reflection j' * P.reflection j) := by
      intro j' j _
      obtain ⟨L, _, _, _, _, hPL⟩ := exists_extension_of_mem_realizationLocus I G i
        (P.reflection j) l (Set.mem_iInter.mp hl.2 j)
      exact isOfFinOrder_mul_of_isRealizedAt I G i L (hclosed L)
        ((isRealizedAt_reflection I G i l Q hQ j').restrict I G i _ (l := l)) hPL
    let e := Langlands.LinearAlgebra.rootDatumEquivOfFiniteOrderReflections Q P
      (CoordinateRootDatum.pairing_eq_of_fields I G i l Q k P hQ hP)
      (CoordinateRootDatum.rootRange_eq_of_weightRanks I G i l Q k P hQ hP
        (hrank _ hl.1)) horder
    exact CoordinateRootDatum.isRootDatumOf_of_identityEquiv l hQ e rfl rfl

end LocalSplitCorootTransport

/-- A split fibrewise maximal torus in a reductive group has one full
coordinate root datum near each point, and the root summands have rank one
at that point. -/
theorem exists_open_coordinateRootDatum
    {R : Type u} [CommRing R]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (p : Spec (CommRingCat.of R)) :
    haveI := hG.isAffineHom
    haveI := hG.smooth
    ∃ (J : Type u) (_ : Finite J) (P : RootDatum J (I → ℤ) (I → ℤ))
      (U : Set (Spec (CommRingCat.of R))), P.IsReduced ∧ IsOpen U ∧ p ∈ U ∧
      (∀ α, splitTorus.exponentWeightRank I G i (P.root α) p = 1) ∧
      ∀ (l : Type u) [Field l] [Algebra R l],
        (algebraBaseMap R l) (IsLocalRing.closedPoint l) ∈ U →
        IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
          (CoordinateRootDatum.fieldRealization l P) := by
  classical
  let := hG.isAffineHom
  let := hG.smooth
  have hmaxK (l : Type u) [Field l] [Algebra R l] :=
    splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax l
  have hfield (l : Type u) [Field l] [Algebra R l] :=
    rootDatumExistence l _ (hG.isConnectedReductive_algebraMap l)
      (splitTorus.commGroupScheme (Spec (CommRingCat.of l)) I)
      (isSplitTorus_splitTorus I) _ (hmaxK l)
  let k := (Spec (CommRingCat.of R)).residueField p
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField p)
  let : Algebra R k := φ.hom.toAlgebra
  have hb : algebraBaseMap R k = (Spec (CommRingCat.of R)).fromSpecResidueField p :=
    Spec.map_preimage _
  have hp : (algebraBaseMap R k) (IsLocalRing.closedPoint k) = p := by
    rw [hb]
    exact Scheme.fromSpecResidueField_apply _ _
  obtain ⟨J, hJ, Q, hQ, hred⟩ := hfield k
  let P := CoordinateRootDatum.ofField k Q
  have hP := CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hQ
  obtain ⟨U, hU, hpU, hUP⟩ :=
    LocalSplitCorootTransport.exists_open_isRootDatumOf I G i
      (fun l _ _ => (hmaxK l).2.1) k P hP
  refine ⟨J, hJ, P, U, CoordinateRootDatum.ofField_isReduced hred, hU,
    hp ▸ hpU, ?_, ?_⟩
  · intro α
    let Gk := (baseChange (algebraBaseMap R k)).obj G
    have : IsAffineHom Gk.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))
    have hroot : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α) ∈
        roots (splitTorus.baseChangeHom (K := k) G I i) :=
      (CoordinateRootDatum.mem_rootRange_iff k P _ hP _).mp ⟨α, rfl⟩
    obtain ⟨e⟩ := splitRootLieLine k Gk (hG.isConnectedReductive_algebraMap k)
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (isSplitTorus_splitTorus I) _ (hmaxK k) _ hroot
    have he := e.finrank_eq
    rw [Module.finrank_self] at he
    rw [← hp, ← splitTorus.finrank_exponentWeightSpace_fieldBaseChange,
      splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter]
    exact he.symm
  · intro l _ _ hl
    obtain ⟨J', _, Q', hQ', -⟩ := hfield l
    exact hUP l hl (CoordinateRootDatum.ofField l Q')
      (CoordinateRootDatum.isRootDatumOf_fieldRealization_ofField hQ')

end Langlands.GroupScheme
