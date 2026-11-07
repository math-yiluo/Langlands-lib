import Langlands.GroupScheme.Reductive.RootDatumAssembly
import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Langlands.GroupScheme.Reductive.RootReducednessStatement
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # The root datum of a split maximal torus from reflection data and the finite Weyl image -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

variable (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- **Uniqueness of the coroot from the finite Weyl image.** If the Weyl image of `i` is
finite, two normalizing points acting on characters by the reflection formula along the same
character `γ`, with cocharacters `c₁`, `c₂` pairing to two with `γ`, have `c₁ = c₂`. -/
theorem coroot_eq_of_weylAction_of_finite_weylImage (hT : IsSplitTorus T.toGrp)
    [Finite (weylImage i)] {γ : characterLattice T} {n₁ n₂ : normalizerPoints i}
    {c₁ c₂ : cocharacterLattice T} (hc₁ : latticePairing T γ c₁ = 2)
    (hc₂ : latticePairing T γ c₂ = 2)
    (h₁ : ∀ χ, weylAction i n₁ χ = χ - latticePairing T χ c₁ • γ)
    (h₂ : ∀ χ, weylAction i n₂ χ = χ - latticePairing T χ c₂ • γ) : c₁ = c₂ := by
  let a : weylImage i := ⟨weylAction i n₁, n₁, rfl⟩
  let b : weylImage i := ⟨weylAction i n₂, n₂, rfl⟩
  have horder : IsOfFinOrder (weylAction i n₁ * weylAction i n₂) := by
    have hfin := (weylImage i).subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
    change IsOfFinOrder (weylAction i n₁ * weylAction i n₂) at hfin
    exact hfin
  have heq : (latticePairing T).flip c₁ = (latticePairing T).flip c₂ :=
    Langlands.LinearAlgebra.eq_functional_of_finiteOrder_reflections γ
      ((latticePairing T).flip c₁) ((latticePairing T).flip c₂) (weylAction i n₁)
      (weylAction i n₂) hc₁ hc₂ h₁ h₂ horder
  have := hT.isPerfPair_latticePairing
  exact (LinearMap.IsPerfPair.bijective_right (latticePairing T)).injective heq

namespace RelativeRootReflectionData

variable {i} (D : RelativeRootReflectionData i)

/-- **Stability of the coroots from the finite Weyl image.** The coroot of `s_α(β)` is
`s_α^∨(β^∨)`. -/
theorem coroot_weylRootPerm_of_finite_weylImage (hT : IsSplitTorus T.toGrp)
    [Finite (weylImage i)] (α β : relativeRoots i) :
    D.coroot (weylRootPerm i (D.representative α) β) = D.reflectedCoroot α β := by
  have h₁ : ∀ χ, weylAction i (D.representative (weylRootPerm i (D.representative α) β)) χ =
      χ - latticePairing T χ (D.coroot (weylRootPerm i (D.representative α) β)) •
        weylAction i (D.representative α) β.val :=
    D.action (weylRootPerm i (D.representative α) β)
  have hc₁ : latticePairing T (weylAction i (D.representative α) β.val)
      (D.coroot (weylRootPerm i (D.representative α) β)) = 2 :=
    D.pair_self (weylRootPerm i (D.representative α) β)
  exact coroot_eq_of_weylAction_of_finite_weylImage i hT hc₁ (D.pairing_reflectedCoroot α β) h₁
    (D.weylAction_conj α β)

/-- The root datum on the actual character and cocharacter lattices built from integral
reflection data when the Weyl image is finite: index type the actual roots, roots the roots
themselves, coroots the reflection cocharacters, pairing `latticePairing T`, and reflection
permutations the Weyl actions of the representatives. -/
def rootDatumOfFiniteWeylImage (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    [Finite (weylImage i)] :
    RootDatum (relativeRoots i) (characterLattice T) (cocharacterLattice T) where
  toLinearMap := latticePairing T
  isPerfPair_toLinearMap := hT.isPerfPair_latticePairing
  root := Function.Embedding.subtype _
  coroot := ⟨D.coroot, D.coroot_injective hT hfinite⟩
  root_coroot_two α := D.pair_self α
  reflectionPerm α := weylRootPerm i (D.representative α)
  reflectionPerm_root α β := (D.action α β.val).symm
  reflectionPerm_coroot α β := (D.coroot_weylRootPerm_of_finite_weylImage hT α β).symm

variable (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite) [Finite (weylImage i)]

@[simp]
theorem rootDatumOfFiniteWeylImage_toLinearMap :
    (D.rootDatumOfFiniteWeylImage hT hfinite).toLinearMap = latticePairing T :=
  rfl

@[simp]
theorem rootDatumOfFiniteWeylImage_root (α : relativeRoots i) :
    (D.rootDatumOfFiniteWeylImage hT hfinite).root α = α.val :=
  rfl

@[simp]
theorem rootDatumOfFiniteWeylImage_coroot (α : relativeRoots i) :
    (D.rootDatumOfFiniteWeylImage hT hfinite).coroot α = D.coroot α :=
  rfl

theorem rootDatumOfFiniteWeylImage_reflection (α : relativeRoots i) :
    (D.rootDatumOfFiniteWeylImage hT hfinite).reflection α =
      weylAction i (D.representative α) := by
  apply LinearEquiv.ext
  intro χ
  rw [D.action, RootPairing.reflection_apply]
  rfl

/-- The root datum built with the finite Weyl image is the root datum of `i`. -/
theorem isRootDatumOf_rootDatumOfFiniteWeylImage :
    IsRootDatumOf i (D.rootDatumOfFiniteWeylImage hT hfinite) := by
  refine ⟨rfl, ?_, fun α => ⟨(D.representative α).val, normalizingAut i (D.representative α),
    isNormalizingPoint_normalizingAut i _, ?_⟩⟩
  · change Set.range (Subtype.val : relativeRoots i → characterLattice T) = roots i
    rw [Subtype.range_coe]
    rfl
  · rw [D.rootDatumOfFiniteWeylImage_reflection]
    rfl

/-- If any two linearly dependent actual roots agree up to sign, the root datum built with the
finite Weyl image is reduced. -/
theorem isReduced_rootDatumOfFiniteWeylImage
    (hred : ∀ α ∈ relativeRoots i, ∀ β ∈ relativeRoots i,
      ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β) :
    (D.rootDatumOfFiniteWeylImage hT hfinite).IsReduced :=
  ⟨fun α β h => hred α.val α.property β.val β.property h⟩

end RelativeRootReflectionData

/-- **Conditional existence of the root datum, with a finite Weyl image.** For a split torus of
a connected reductive group with finite Weyl image, integral reflection data and reducedness
in the form of `RootPairing.IsReduced` give a finite reduced root datum of `i`. -/
theorem exists_rootDatum_of_reflectionData_of_finite_weylImage (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (D : RelativeRootReflectionData i) [Finite (weylImage i)]
    (hred : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β) :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      IsRootDatumOf i P ∧ P.IsReduced := by
  have := hG.smooth
  have hfinite := hT.finite_relativeRoots i
  exact ⟨relativeRoots i, hfinite.to_subtype, D.rootDatumOfFiniteWeylImage hT hfinite,
    D.isRootDatumOf_rootDatumOfFiniteWeylImage hT hfinite,
    D.isReduced_rootDatumOfFiniteWeylImage hT hfinite hred⟩

/-- **Existence of the root datum from reflection existence and reducedness.** The published
root-datum existence proposition follows from intrinsic integral reflection existence and root
reducedness; the finiteness of the Weyl image is the published `splitTorusWeylImageFinite`. -/
theorem rootDatumExistence_of_reflectionExistence_of_reducedness
    (hrefl : RelativeRootReflectionExistenceStatement.{u})
    (hred : RootReducednessStatement.{u}) : RootDatumExistenceStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  have hi' : IsMaximalSplitTorus i := hi.isMaximalSplitTorus hT
  have := hi'.isSplitSubtorus.mono
  obtain ⟨D, -⟩ := hrefl k G hG T i hi'
  have := hG.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi.2.1
  exact exists_rootDatum_of_reflectionData_of_finite_weylImage i hG hT D (hred k G hG T hT i hi)

end Langlands.GroupScheme
