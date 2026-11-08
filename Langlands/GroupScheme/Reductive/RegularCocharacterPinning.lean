import Langlands.GroupScheme.Reductive.RootDatumGaloisSimpleRoots
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.LinearAlgebra.RootDatumCoweightFace

/-! # Positive bases and split pinnings from regular cocharacters -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace RootPairing.Base

variable {J : Type v} [Finite J] {M N : Type w} [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N) (b : P.Base)

/-- An integral functional positive on the simple roots detects exactly the
positive roots of the base. -/
theorem isPos_iff_positive_functional (f : Module.Dual ℤ M)
    (hf : ∀ i ∈ b.support, 0 < f (P.root i)) (i : J) :
    b.IsPos i ↔ 0 < f (P.root i) := by
  have hforward (j : J) (hj : b.IsPos j) : 0 < f (P.root j) := by
    apply hj.induction_on_add
    · exact hf
    · intro a c z hz ha hc
      rw [hz, map_add]
      exact add_pos ha (hf c hc)
  constructor
  · exact hforward i
  · intro hi
    let := P.indexNeg
    rcases RootPairing.Base.IsPos.or_neg b i with hp | hn
    · exact hp
    · have hneg := hforward (-i) hn
      have heq : P.root (-i) = -P.root i := by simp
      rw [heq, map_neg] at hneg
      omega

end RootPairing.Base

namespace Langlands.GroupScheme

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i

local instance regularCocharacterPinningBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {J : Type u} [Finite J]
    {P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i) P)
    [P.IsReduced]
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hν : ∀ a, P.root' a ν ≠ 0)

/-- Choose a genuine integral base with the positive roots specified by the
supplied regular cocharacter. -/
def IsRootDatumOf.regularCocharacterBase : P.Base := by
  let := Fintype.ofFinite J
  exact (Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P ν hν).choose

/-- The selected support consists of the indecomposable positive roots for the
original supplied cocharacter. -/
theorem IsRootDatumOf.regularCocharacterBase_support :
    ((IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν).support : Set J) =
      IsAddIndecomposable.baseOf P.root ((P.flip.toLinearMap ν) : _ →+ ℤ) := by
  let := Fintype.ofFinite J
  exact (Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P ν hν).choose_spec

include hP in
/-- Positivity for the selected base is precisely strict positivity of the
actual integral character/cocharacter pairing. -/
theorem IsRootDatumOf.regularCocharacterBase_isPos (a : J) :
    (IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν).IsPos a ↔
      0 < latticePairing T_K (P.root a) ν := by
  rw [← hP.1]
  apply RootPairing.Base.isPos_iff_positive_functional P _ (P.flip.toLinearMap ν)
  intro c hc
  have hmem : c ∈ IsAddIndecomposable.baseOf P.root
      ((P.flip.toLinearMap ν) : _ →+ ℤ) := by
    rw [← IsRootDatumOf.regularCocharacterBase_support k K (P := P) ν hν]
    exact hc
  exact hmem.1

variable (hfixed : ∀ σ : K ≃ₐ[k] K,
    cocharacterLattice.galoisRepresentation k K T σ ν = ν)

include hfixed in
/-- A fixed regular cocharacter makes the chosen positive roots stable under
the ordinary Galois action, with no Weyl correction. -/
theorem IsRootDatumOf.galoisRootIndexEquiv_regularCocharacterBase_isPos
    (σ : K ≃ₐ[k] K) (a : J) :
    (IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν).IsPos
        (IsRootDatumOf.galoisRootIndexEquiv k K i hP σ a) ↔
      (IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν).IsPos a := by
  rw [IsRootDatumOf.regularCocharacterBase_isPos k K i hP,
    IsRootDatumOf.regularCocharacterBase_isPos k K i hP,
    IsRootDatumOf.galoisRootIndexEquiv_root]
  have heq := latticePairing_galoisRepresentation k K T σ (P.root a) ν
  rw [hfixed σ] at heq
  rw [heq]

/-- Restrict the ordinary root-index representation to the base constructed
from the fixed regular cocharacter. -/
def IsRootDatumOf.regularCocharacterSimpleAction :
    (K ≃ₐ[k] K) →* Equiv.Perm
      (IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν).support where
  toFun σ := Equiv.subtypeEquiv (IsRootDatumOf.galoisRootIndexEquiv k K i hP σ)
    (fun a => (RootPairing.Base.mem_support_equiv_iff_of_isPos P _
      (IsRootDatumOf.galoisRootIndexEquiv k K i hP σ)
      (characterLattice.galoisEquiv k K T σ)
      (IsRootDatumOf.galoisRootIndexEquiv_root k K i hP σ)
      (IsRootDatumOf.galoisRootIndexEquiv_regularCocharacterBase_isPos
        k K i hP ν hν hfixed σ) a).symm)
  map_one' := by
    ext a
    exact congrArg (fun e : Equiv.Perm J => e a.val)
      (map_one (IsRootDatumOf.galoisRootIndexAction k K i hP))
  map_mul' σ τ := by
    ext a
    exact congrArg (fun e : Equiv.Perm J => e a.val)
      (map_mul (IsRootDatumOf.galoisRootIndexAction k K i hP) σ τ)

/-- The constructed simple-root action satisfies the actual ordinary
character transport law. -/
@[simp]
theorem IsRootDatumOf.regularCocharacterSimpleAction_root
    (σ : K ≃ₐ[k] K)
    (a : (IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν).support) :
    P.root (IsRootDatumOf.regularCocharacterSimpleAction k K i hP ν hν hfixed σ a) =
      characterLattice.galoisRepresentation k K T σ (P.root a) :=
  IsRootDatumOf.galoisRootIndexEquiv_root k K i hP σ a

/-- A regular cocharacter over the ground field supplies the fixedness required
for the ordinary simple-root action after canonical base change. -/
def IsRootDatumOf.descendedRegularCocharacterSimpleAction
    (ν₀ : cocharacterLattice T)
    (hν₀ : ∀ a, P.root' a (cocharacterLattice.baseChange b T ν₀) ≠ 0) :
    (K ≃ₐ[k] K) →* Equiv.Perm
      (IsRootDatumOf.regularCocharacterBase k K (P := P)
        (cocharacterLattice.baseChange b T ν₀) hν₀).support :=
  IsRootDatumOf.regularCocharacterSimpleAction k K i hP
    (cocharacterLattice.baseChange b T ν₀) hν₀
    (fun σ => cocharacterLattice.galoisRepresentation_baseChange k K T σ ν₀)

/-- The action constructed from a ground-field cocharacter transports actual
roots by the ordinary character representation. -/
@[simp]
theorem IsRootDatumOf.descendedRegularCocharacterSimpleAction_root
    (ν₀ : cocharacterLattice T)
    (hν₀ : ∀ a, P.root' a (cocharacterLattice.baseChange b T ν₀) ≠ 0)
    (σ : K ≃ₐ[k] K)
    (a : (IsRootDatumOf.regularCocharacterBase k K (P := P)
      (cocharacterLattice.baseChange b T ν₀) hν₀).support) :
    P.root
        (IsRootDatumOf.descendedRegularCocharacterSimpleAction k K i hP ν₀ hν₀ σ a) =
      characterLattice.galoisRepresentation k K T σ (P.root a) :=
  IsRootDatumOf.galoisRootIndexEquiv_root k K i hP σ a

/-- Construct the initial actual split pinning with the prescribed regular
cocharacter base; the simple-root trivializations are constructed from the
proved root-line theorem. -/
def IsRootDatumOf.regularCocharacterPinning
    (hG : IsConnectedReductive G_K) (hT : IsSplitTorus (T_K).toGrp)
    (hi : IsMaximalTorus (T := T_K) i_K) : SplitPinning G_K where
  isConnectedReductive := hG
  torus := T_K
  inclusion := i_K
  isSplitTorus := hT
  isMaximalTorus := hi
  rootIndex := J
  rootDatum := P
  isRootDatum := hP
  isReduced := inferInstance
  base := IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν
  pinning := RootPinning.ofSplitMaximalTorus hG hT i_K hi P hP
    (IsRootDatumOf.regularCocharacterBase k K (P := P) ν hν)

end Langlands.GroupScheme
