import Langlands.GroupScheme.Rational.SteinbergCompatiblePinning
import Langlands.GroupScheme.Reductive.RegularCocharacterPinning
import Langlands.GroupScheme.Rational.TorusCentralizerRegularCocharacter
import Langlands.GroupScheme.Rational.SteinbergGaloisOrbitBlocks
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Galois-compatible pinnings of quasi-split groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.GroupScheme

section Regular

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- A regular cocharacter pairs nonzero with every root of a root datum of the
same torus inclusion. -/
theorem IsRootDatumOf.root'_ne_zero_of_isRegularCocharacter (hP : IsRootDatumOf i P)
    {ν : cocharacterLattice T} (hν : IsRegularCocharacter i ν) (a : J) :
    P.root' a ν ≠ 0 := by
  have h := hν (P.root a) (hP.2.1 ▸ Set.mem_range_self a)
  rwa [← hP.1] at h

end Regular

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => CategoryTheory.Functor.obj
  (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance instIsAffineHomBaseChange_quasiSplitCompatiblePinning : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- An actual split pinning of `G_K` whose torus is the base change of a torus
of `G` over `k`, together with an ordinary Galois action on its simple roots
transporting the actual roots, compatible pinning vectors, and normalized whole
root maps compatible with that action. -/
structure GaloisCompatiblePinningData where
  /-- The actual split pinning over `K`. -/
  pinning : SplitPinning G_K
  /-- The descended torus over `k`. -/
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  /-- The descended torus inclusion over `k`. -/
  inclusion : torus.toGrp ⟶ G
  /-- The pinning torus is the base change of the descended torus. -/
  torusIso : pinning.torus ≅ (CommGroupScheme.baseChange (algebraBaseMap k K)).obj torus
  /-- The pinning inclusion is the base change of the descended inclusion. -/
  inclusion_eq : pinning.inclusion = CommGroupScheme.groupHom torusIso.hom ≫
    (GroupScheme.baseChange (algebraBaseMap k K)).map inclusion
  /-- The ordinary Galois action on the simple roots. -/
  action : (K ≃ₐ[k] K) →* Equiv.Perm pinning.base.support
  /-- The action transports the actual simple roots by ordinary coefficient
  transport of characters of the descended torus. -/
  action_root : ∀ (σ : K ≃ₐ[k] K) (a : pinning.base.support),
    characterLattice.congr torusIso (pinning.rootDatum.root (action σ a)) =
      characterLattice.galoisRepresentation k K torus σ
        (characterLattice.congr torusIso (pinning.rootDatum.root a))
  /-- The pinning vectors are compatible with semilinear Lie transport. -/
  rootVectors_compatible : SplitPinning.RootVectorsGaloisCompatible k K pinning action
  /-- Normalized whole simple-root maps. -/
  rootMaps : pinning.NormalizedSimpleRootParametrizations
  /-- The whole root maps are compatible with the action. -/
  rootMaps_compatible : SplitPinning.RootMapsGaloisCompatible k K pinning rootMaps action

namespace GaloisCompatiblePinningData

variable {k K G}

/-- Under orthogonality of the simple-root orbits, the full image ideal of the
canonical Steinberg product in orbit order descends to the ground field. -/
def definingIdealDescent [IsGalois k K] (D : GaloisCompatiblePinningData k K G)
    (horth : D.pinning.OrthogonalSimpleOrbits D.action) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      (SplitPinning.steinbergProduct (D.pinning.simpleOrbitOrdering D.action) D.rootMaps
        (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps)).left.ker :=
  SteinbergOrbitImageDescent.definingIdealDescent_of_orthogonalSimpleOrbits k K G D.pinning
    D.inclusion D.torusIso D.inclusion_eq D.rootMaps D.action D.action_root
    D.rootMaps_compatible horth

section OfRegular

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

variable {J : Type u} [Finite J]
    {P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
    (hP : IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k K)).map i) P)
    [P.IsReduced]
    (ν₀ : cocharacterLattice T)
    (hν : ∀ a, P.root' a (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) ≠ 0)
    (hG : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))

/-- The initial pinning from a ground-field regular cocharacter has the base
change of the ground-field inclusion as its inclusion. -/
theorem regularCocharacterPinning_inclusion_eq :
    (IsRootDatumOf.regularCocharacterPinning k K i hP
        (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi).inclusion =
      CommGroupScheme.groupHom
          (Iso.refl ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)).hom ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map i := by
  have hid : CommGroupScheme.groupHom
      (𝟙 ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) =
        𝟙 ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp := rfl
  rw [Iso.refl_hom, hid, Category.id_comp]
  rfl

/-- The descended ordinary simple-root action transports the actual roots of the
initial pinning. -/
theorem regularCocharacterPinning_action_root (σ : K ≃ₐ[k] K)
    (a : (IsRootDatumOf.regularCocharacterPinning k K i hP
        (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi).base.support) :
    characterLattice.congr (Iso.refl _)
        ((IsRootDatumOf.regularCocharacterPinning k K i hP
          (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi).rootDatum.root
          (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν σ a : J)) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr (Iso.refl _)
          ((IsRootDatumOf.regularCocharacterPinning k K i hP
            (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi).rootDatum.root
            a)) := by
  simp only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp]
  exact IsRootDatumOf.descendedRegularCocharacterSimpleAction_root k K i hP ν₀ hν σ a

/-- Build Galois-compatible pinning data from a ground-field cocharacter that is
regular after base change: the base is the one prescribed by the cocharacter,
the action is the ordinary Galois action on roots, and the pinning vectors and
whole root maps are chosen compatibly. -/
def ofRegularCocharacter [FiniteDimensional k K] : GaloisCompatiblePinningData k K G where
  pinning := SplitPinning.galoisCompatibleRepinning k K
    (IsRootDatumOf.regularCocharacterPinning k K i hP
      (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi) i
    (Iso.refl ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (regularCocharacterPinning_inclusion_eq i hP ν₀ hν hG hT hi)
    (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν)
    (regularCocharacterPinning_action_root i hP ν₀ hν hG hT hi)
  torus := T
  inclusion := i
  torusIso := Iso.refl ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
  inclusion_eq := regularCocharacterPinning_inclusion_eq i hP ν₀ hν hG hT hi
  action := IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν
  action_root := regularCocharacterPinning_action_root i hP ν₀ hν hG hT hi
  rootVectors_compatible := SplitPinning.galoisCompatibleRepinning_rootVectors k K
    (IsRootDatumOf.regularCocharacterPinning k K i hP
      (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi) i
    (Iso.refl ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (regularCocharacterPinning_inclusion_eq i hP ν₀ hν hG hT hi)
    (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν)
    (regularCocharacterPinning_action_root i hP ν₀ hν hG hT hi)
  rootMaps := SplitPinning.galoisCompatibleRootParametrizations k K
    (IsRootDatumOf.regularCocharacterPinning k K i hP
      (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi) i
    (Iso.refl ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (regularCocharacterPinning_inclusion_eq i hP ν₀ hν hG hT hi)
    (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν)
    (regularCocharacterPinning_action_root i hP ν₀ hν hG hT hi)
  rootMaps_compatible := SplitPinning.galoisCompatibleRootParametrizations_compatible k K
    (IsRootDatumOf.regularCocharacterPinning k K i hP
      (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν hG hT hi) i
    (Iso.refl ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (regularCocharacterPinning_inclusion_eq i hP ν₀ hν hG hT hi)
    (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν)
    (regularCocharacterPinning_action_root i hP ν₀ hν hG hT hi)

/-- The positive roots of the constructed pinning are exactly the roots pairing
positively with the base change of the ground-field cocharacter. -/
theorem ofRegularCocharacter_isPos [FiniteDimensional k K] (a : J) :
    (ofRegularCocharacter i hP ν₀ hν hG hT hi).pinning.base.IsPos a ↔
      0 < latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) (P.root a)
        (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) :=
  IsRootDatumOf.regularCocharacterBase_isPos k K i hP _ hν a

end OfRegular

end GaloisCompatiblePinningData

namespace TorusCentralizerTorusData

variable {k K G} {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (C : TorusCentralizerTorusData a) [LocallyOfFiniteType G.X.hom]

/-- An actual torus centralizer of a split torus in a connected reductive group
yields Galois-compatible pinning data over every finite extension splitting the
centralizer torus, given existence of root data of split reductive groups. -/
theorem nonempty_galoisCompatiblePinningData [FiniteDimensional k K]
    (hA : IsSplitTorus A.toGrp) (hG : IsConnectedReductive G)
    (hRDE : RootDatumExistenceStatement.{u})
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj C.torus).toGrp) :
    Nonempty (GaloisCompatiblePinningData k K G) := by
  have hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    hRDE K ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) hGK _ hT _
      (C.isMaximalTorus_baseChange K)
  let : Finite J := hJ
  let : P.IsReduced := hred
  exact ⟨GaloisCompatiblePinningData.ofRegularCocharacter C.inclusion hP
    (C.regularCocharacter hA)
    (hP.root'_ne_zero_of_isRegularCocharacter
      (C.regularCocharacter_baseChange_isRegular K hA hT))
    hGK hT (C.isMaximalTorus_baseChange K)⟩

end TorusCentralizerTorusData

variable {k G}

/-- A quasi-split group has Galois-compatible pinning data over some finite
Galois extension, conditional only on the parabolic dynamic statement and the
existence of root data of split reductive groups. -/
theorem IsQuasiSplit.exists_galoisCompatiblePinningData
    (hPD : ParabolicDynamicStatement.{u}) (hRDE : RootDatumExistenceStatement.{u})
    (hG : IsQuasiSplit G) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧
      IsGalois k K ∧ Nonempty (GaloisCompatiblePinningData k K G) := by
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  obtain ⟨A, a, ha, C, c, hc, hclosed, hC⟩ :=
    hG.exists_maximalSplitTorus_with_torusCentralizer dynamicCentralizerReductive hPD
  let D : TorusCentralizerTorusData a :=
    { torus := { toGrp := C, comm := hC.isCommMonObj }
      inclusion := c
      isTorus := hC
      isClosedSubgroup := hclosed
      represents := hc }
  obtain ⟨K, hK, hAK, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k C hC
  let : Field K := hK
  let : Algebra k K := hAK
  let : FiniteDimensional k K := hfin
  exact ⟨K, hK, hAK, hfin, hgal,
    D.nonempty_galoisCompatiblePinningData ha.1.1 hG.isConnectedReductive hRDE hsplit⟩

end Langlands.GroupScheme
