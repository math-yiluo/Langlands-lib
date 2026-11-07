import Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.LinearAlgebra.RootDatumOrbitPairs

/-! # Simple-root orbits of Galois-compatible pinnings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LinearAlgebra.RootDatumOrbitPairs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Langlands.GroupScheme

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {J : Type u}
    {P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}

/-- The ordinary Galois permutation of the roots of a closed split torus
preserves the integral pairing. -/
theorem IsRootDatumOf.galoisRootIndexEquiv_pairing
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left)
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) P)
    (σ : K ≃ₐ[k] K) (a c : J) :
    P.pairing (IsRootDatumOf.galoisRootIndexEquiv k K i hP σ a)
        (IsRootDatumOf.galoisRootIndexEquiv k K i hP σ c) = P.pairing a c :=
  (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k K i hT hi hP σ).toHom.pairing

variable [Finite J]
    (hP : IsRootDatumOf ((GroupScheme.baseChange (algebraBaseMap k K)).map i) P)
    [P.IsReduced]
    (ν₀ : cocharacterLattice T)
    (hν : ∀ a, P.root' a (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) ≠ 0)

/-- The descended ordinary simple-root action is the restriction of the
pairing-preserving Galois permutation of all roots. -/
theorem IsRootDatumOf.descendedRegularCocharacterSimpleAction_isPairingCompatible
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hi : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left) :
    IsPairingCompatible
      (IsRootDatumOf.regularCocharacterBase k K (P := P)
        (cocharacterLattice.baseChange (algebraBaseMap k K) T ν₀) hν)
      (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν) :=
  fun σ => ⟨IsRootDatumOf.galoisRootIndexEquiv k K i hP σ,
    fun a c => IsRootDatumOf.galoisRootIndexEquiv_pairing k K i hT hi hP σ a c,
    fun _ => rfl⟩

/-- Galois-compatible pinning data whose simple-root action is the restriction
of a pairing-preserving permutation of all roots, for every Galois element. -/
structure PairingCompatiblePinningData (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    extends GaloisCompatiblePinningData k K G where
  /-- The simple-root action extends to pairing-preserving root permutations. -/
  isPairingCompatible : IsPairingCompatible pinning.base action

variable {k K i hP ν₀ hν}

namespace GaloisCompatiblePinningData

variable (hG : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))

/-- The constructed simple-root action is pairing-compatible. -/
theorem ofRegularCocharacter_isPairingCompatible [FiniteDimensional k K] :
    IsPairingCompatible (ofRegularCocharacter i hP ν₀ hν hG hT hi).pinning.base
      (ofRegularCocharacter i hP ν₀ hν hG hT hi).action :=
  IsRootDatumOf.descendedRegularCocharacterSimpleAction_isPairingCompatible k K i hP ν₀ hν hT
    hi.2.1

end GaloisCompatiblePinningData

namespace PairingCompatiblePinningData

variable (hG : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))

/-- The data built from a regular ground-field cocharacter, with its
pairing-compatible action. -/
def ofRegularCocharacter [FiniteDimensional k K] : PairingCompatiblePinningData k K G where
  toGaloisCompatiblePinningData :=
    GaloisCompatiblePinningData.ofRegularCocharacter i hP ν₀ hν hG hT hi
  isPairingCompatible :=
    GaloisCompatiblePinningData.ofRegularCocharacter_isPairingCompatible hG hT hi

end PairingCompatiblePinningData

namespace TorusCentralizerTorusData

variable {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (C : TorusCentralizerTorusData a)

/-- An actual torus centralizer yields Galois-compatible pinning data with a
pairing-compatible simple-root action over every finite extension splitting the
centralizer torus, given existence of root data of split reductive groups. -/
theorem nonempty_pairingCompatiblePinningData [FiniteDimensional k K]
    (hA : IsSplitTorus A.toGrp) (hG : IsConnectedReductive G)
    (hRDE : RootDatumExistenceStatement.{u})
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj C.torus).toGrp) :
    Nonempty (PairingCompatiblePinningData k K G) := by
  have hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    hRDE K ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) hGK _ hT _
      (C.isMaximalTorus_baseChange K)
  let : Finite J := hJ
  let : P.IsReduced := hred
  exact ⟨PairingCompatiblePinningData.ofRegularCocharacter
    (hP := hP) (ν₀ := C.regularCocharacter hA)
    (hν := hP.root'_ne_zero_of_isRegularCocharacter
      (C.regularCocharacter_baseChange_isRegular K hA hT))
    hGK hT (C.isMaximalTorus_baseChange K)⟩

end TorusCentralizerTorusData

omit [LocallyOfFiniteType G.X.hom] in
/-- A quasi-split group has Galois-compatible pinning data with a
pairing-compatible simple-root action over some finite Galois extension,
conditional only on the parabolic dynamic statement and the existence of root
data of split reductive groups. -/
theorem IsQuasiSplit.exists_pairingCompatiblePinningData
    (hPD : ParabolicDynamicStatement.{u}) (hRDE : RootDatumExistenceStatement.{u})
    (hG : IsQuasiSplit G) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧
      IsGalois k K ∧ Nonempty (PairingCompatiblePinningData k K G) := by
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
    D.nonempty_pairingCompatiblePinningData ha.1.1 hG.isConnectedReductive hRDE hsplit⟩

namespace PairingCompatiblePinningData

variable {G' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G'.X.hom]
    (D : PairingCompatiblePinningData k K G')

/-- Either the simple-root orbits are orthogonal, or some orbit contains an
`A₂` pair swapped by the moving Galois element. -/
theorem orthogonalSimpleOrbits_or_exists_pair :
    D.pinning.OrthogonalSimpleOrbits D.action ∨
      ∃ (σ : K ≃ₐ[k] K) (a : D.pinning.base.support), D.action σ a ≠ a ∧
        D.pinning.rootDatum.pairing a (D.action σ a) = -1 ∧
        D.pinning.rootDatum.pairing (D.action σ a) a = -1 ∧
        D.action σ (D.action σ a) = a := by
  have hD := D.isPairingCompatible
  by_cases h : ∀ (σ : K ≃ₐ[k] K) (a : D.pinning.base.support), D.action σ a ≠ a →
      D.pinning.rootDatum.pairing a (D.action σ a) ≠ -1
  · exact Or.inl fun σ a hσ => isOrthogonal_of_forall_pairing_ne_neg_one hD h σ a hσ
  · right
    push Not at h
    obtain ⟨σ, a, hσ, hpair⟩ := h
    have hno : ¬ D.pinning.rootDatum.IsOrthogonal a (D.action σ a) := fun ho => by
      rw [ho.1] at hpair
      norm_num at hpair
    exact ⟨σ, a, hσ, (pairing_eq_neg_one_of_not_isOrthogonal hD a hσ hno).1,
      (pairing_eq_neg_one_of_not_isOrthogonal hD a hσ hno).2,
      apply_apply_eq_of_not_isOrthogonal hD a hσ hno⟩

end PairingCompatiblePinningData

end Langlands.GroupScheme
