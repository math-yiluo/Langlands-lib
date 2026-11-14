import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Diagonalizable groups and groups of multiplicative type over a base scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- The diagonalizable group `D_S(Λ)` over a scheme `S`: the base change along `S ⟶ Spec ℤ`
of the diagonalizable group `D(Λ) = Spec ℤ[Λ]` over `Spec ℤ`. Its points over an `S`-scheme
`T` are the homomorphisms `Λ → Γ(T, 𝒪_T)ˣ`. -/
abbrev diagonalizable (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] : GroupScheme S :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).obj
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).toGrp

/-- A group scheme over `S` is **diagonalizable** (split of multiplicative type) if it is
isomorphic to `D_S(Λ)` for a finitely generated abelian group `Λ`. -/
def IsDiagonalizable (H : GroupScheme S) : Prop :=
  ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
    Nonempty (H ≅ diagonalizable S Λ)

/-- A group scheme over `S` is **of multiplicative type** (Conrad 2014, Definition B.1.1) if
there is an fppf cover of `S` over each member of which it becomes diagonalizable. -/
def IsMultiplicativeType (H : GroupScheme S) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S,
    ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H)

/-- The base change of `D_S(Λ)` along `b : S' ⟶ S` is `D_{S'}(Λ)`, since both are base changes
of `D(Λ)` from `Spec ℤ` and `Spec ℤ` is terminal. -/
def diagonalizableBaseChangeIso (b : S' ⟶ S) (Λ : Type u) [AddCommGroup Λ] :
    (GroupScheme.baseChange b).obj (diagonalizable S Λ) ≅ diagonalizable S' Λ :=
  (baseChangeCompIso (Gm.toSpecZ S) b _).symm ≪≫
    eqToIso (by rw [specULiftZIsTerminal.hom_ext (b ≫ Gm.toSpecZ S) (Gm.toSpecZ S')])

/-- Diagonalizability is invariant under group-scheme isomorphisms over the base. -/
theorem IsDiagonalizable.of_iso (e : G ≅ H) (hH : IsDiagonalizable H) : IsDiagonalizable G := by
  obtain ⟨Λ, _, hΛ, ⟨f⟩⟩ := hH
  exact ⟨Λ, inferInstance, hΛ, ⟨e ≪≫ f⟩⟩

/-- Diagonalizable groups remain diagonalizable, with the same character group, after
arbitrary base change. -/
theorem IsDiagonalizable.baseChange (b : S' ⟶ S) (hG : IsDiagonalizable G) :
    IsDiagonalizable ((GroupScheme.baseChange b).obj G) := by
  obtain ⟨Λ, _, hΛ, ⟨e⟩⟩ := hG
  exact ⟨Λ, inferInstance, hΛ,
    ⟨(GroupScheme.baseChange b).mapIso e ≪≫ diagonalizableBaseChangeIso b Λ⟩⟩

/-- Being of multiplicative type is invariant under group-scheme isomorphisms over the base. -/
theorem IsMultiplicativeType.of_iso (e : G ≅ H) (hH : IsMultiplicativeType H) :
    IsMultiplicativeType G := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  exact ⟨𝒰, fun i =>
    IsDiagonalizable.of_iso ((GroupScheme.baseChange (𝒰.f i)).mapIso e) (h𝒰 i)⟩

/-- Diagonalizable groups are of multiplicative type, using the identity cover. -/
theorem IsMultiplicativeType.of_isDiagonalizable (hG : IsDiagonalizable G) :
    IsMultiplicativeType G := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun _ => ⟨inferInstance, inferInstance⟩⟩
  exact ⟨Scheme.coverOfIsIso (P := @Flat ⊓ @LocallyOfFinitePresentation) (𝟙 S),
    fun _ => hG.baseChange (𝟙 S)⟩

/-- Groups of multiplicative type remain of multiplicative type after arbitrary base
change. -/
theorem IsMultiplicativeType.baseChange (b : S' ⟶ S) (hG : IsMultiplicativeType G) :
    IsMultiplicativeType ((GroupScheme.baseChange b).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰.pullback₁ b, fun i => ?_⟩
  change IsDiagonalizable
    ((GroupScheme.baseChange (pullback.fst b (𝒰.f i))).obj ((GroupScheme.baseChange b).obj G))
  let e :=
    Descent.pullbackComparison b (pullback.fst b (𝒰.f i))
      (pullback.snd b (𝒰.f i) ≫ 𝒰.f i) pullback.condition G ≪≫
      baseChangeCompIso (𝒰.f i) (pullback.snd b (𝒰.f i)) G
  exact IsDiagonalizable.of_iso e ((h𝒰 i).baseChange (pullback.snd b (𝒰.f i)))

end Langlands.GroupScheme.RelativeMultiplicativeType
