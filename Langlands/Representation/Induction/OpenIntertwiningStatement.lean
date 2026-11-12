import Langlands.Representation.Induction.OpenAdjunction
import Mathlib.GroupTheory.DoubleCoset

/-! # Intertwining kernels of compact induction from an open subgroup: statements

Vignéras 1996, I.8.5, for `K = H`: maps `c-Ind_H^G σ → c-Ind_H^G τ` correspond to
functions `Φ : G → Hom_R(V, W)` with `Φ (h g h') = τ h ∘ Φ g ∘ σ h'`, through
`Φ g v = T (i_v) g`, where `i_v` is the published `unitFunction` (support `H`, value
`σ h v` at `h`). For compact open `H` such a function is determined by its values at
double-coset representatives, each value intertwining `σ` with the `g`-conjugate of `τ`
on `H ∩ g⁻¹ H g`; for finitely generated `σ` the support is a finite union of double
cosets. The declarations are statements only.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW

/-- Intertwining kernels for compact induction from `H`: the covariance
`Φ (h * g * h') = τ h ∘ₗ Φ g ∘ₗ σ h'` of Vignéras I.8.5 b), and, for every vector `v`,
finitely many right cosets `H g` with `Φ g v ≠ 0`. -/
def IsIntertwiningKernel {R : Type uR} {G : Type uG} [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (σ : Representation R H V) (τ : Representation R H W) (Φ : G → V →ₗ[R] W) : Prop :=
  (∀ (h h' : H) (g : G), Φ ((h : G) * g * (h' : G)) = τ h ∘ₗ Φ g ∘ₗ σ h') ∧
    ∀ v : V, (quotientSupport H (fun g => Φ g v)).Finite

/-- A family of values at the double-coset representatives `s q`: each value
intertwines `σ` with the `s q`-conjugate of `τ` on `H ∩ (s q)⁻¹ H (s q)`, and for every
vector `v` only finitely many values are nonzero at `v`. -/
def IsLocalIntertwinerFamily {R : Type uR} {G : Type uG} [CommRing R] [Group G]
    (H : Subgroup G)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (σ : Representation R H V) (τ : Representation R H W)
    (s : DoubleCoset.Quotient (H : Set G) (H : Set G) → G)
    (φ : DoubleCoset.Quotient (H : Set G) (H : Set G) → V →ₗ[R] W) : Prop :=
  (∀ (q : DoubleCoset.Quotient (H : Set G) (H : Set G)) (h : H)
      (hq : s q * (h : G) * (s q)⁻¹ ∈ H),
      φ q ∘ₗ σ h = τ ⟨s q * (h : G) * (s q)⁻¹, hq⟩ ∘ₗ φ q) ∧
    ∀ v : V, {q | φ q v ≠ 0}.Finite

/-- Vignéras I.8.5 for an open subgroup `K = H`: for smooth representations `A` and `B`
of an open subgroup `H`, every map `T : c-Ind A ⟶ c-Ind B` has the intertwining kernel
`Φ g v = T (unitFunction v) g`, and every intertwining kernel arises from exactly one
such map. -/
def CompactInductionKernelStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    (A B : Langlands.SmoothRep.{uR, uG, max uG uV} R H),
    (∀ T : (smoothCompactInduction R H).obj A ⟶ (smoothCompactInduction R H).obj B,
      ∃ Φ : G → (A →ₗ[R] B), IsIntertwiningKernel H A.representation B.representation Φ ∧
        ∀ (g : G) (v : A), Φ g v =
          eval H B.representation
            (SmoothRep.hom T (unitFunction H hH A.representation A.isSmooth v)).1 g) ∧
    ∀ Φ : G → (A →ₗ[R] B), IsIntertwiningKernel H A.representation B.representation Φ →
      ∃! T : (smoothCompactInduction R H).obj A ⟶ (smoothCompactInduction R H).obj B,
        ∀ (g : G) (v : A), Φ g v =
          eval H B.representation
            (SmoothRep.hom T (unitFunction H hH A.representation A.isSmooth v)).1 g

/-- The double-coset decomposition of intertwining kernels for a compact open subgroup
`H` and a smooth representation `σ`: for a choice `s` of double-coset representatives,
restriction `Φ ↦ (q ↦ Φ (s q))` sends intertwining kernels to local intertwiner
families, and every local intertwiner family is the restriction of exactly one
intertwining kernel. -/
def CompactInductionDoubleCosetStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) →
    ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
      (σ : Representation R H V) (τ : Representation R H W), IsSmooth σ →
      ∀ s : DoubleCoset.Quotient (H : Set G) (H : Set G) → G,
        (∀ q, DoubleCoset.mk H H (s q) = q) →
        (∀ Φ : G → V →ₗ[R] W, IsIntertwiningKernel H σ τ Φ →
          IsLocalIntertwinerFamily H σ τ s (fun q => Φ (s q))) ∧
        ∀ φ : DoubleCoset.Quotient (H : Set G) (H : Set G) → V →ₗ[R] W,
          IsLocalIntertwinerFamily H σ τ s φ →
            ∃! Φ : G → V →ₗ[R] W, IsIntertwiningKernel H σ τ Φ ∧ ∀ q, Φ (s q) = φ q

/-- Vignéras I.8.5 a), b) for a compact open subgroup `H` and a finitely generated
representation `σ`: a function `Φ : G → Hom_R(V, W)` is an intertwining kernel exactly
when it has the covariance b) and its support meets only finitely many double cosets
`H g H`. -/
def CompactInductionFiniteTypeKernelStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) →
    ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
      (σ : Representation R H V) (τ : Representation R H W),
      Module.Finite (MonoidAlgebra R H) σ.asModule →
      ∀ Φ : G → V →ₗ[R] W,
        IsIntertwiningKernel H σ τ Φ ↔
          (∀ (h h' : H) (g : G), Φ ((h : G) * g * (h' : G)) = τ h ∘ₗ Φ g ∘ₗ σ h') ∧
            (DoubleCoset.mk H H '' Function.support Φ).Finite

/-- The three compact-induction intertwining statements together. -/
def CompactInductionIntertwiningStatement : Prop :=
  CompactInductionKernelStatement.{uR, uG, uV} ∧
    CompactInductionDoubleCosetStatement.{uR, uG, uV, uW} ∧
    CompactInductionFiniteTypeKernelStatement.{uR, uG, uV, uW}

end Langlands.Induction
