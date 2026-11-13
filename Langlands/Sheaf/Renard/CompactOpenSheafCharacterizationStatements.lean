import Langlands.Sheaf.Renard.ProjectorPresheaf
import Langlands.Sheaf.Renard.LocallyConstantScalarSheaf
import Langlands.HarmonicAnalysis.PointwiseTestAlgebra

/-!
# Sheaves on a t.d. space as unions of compactly supported sections (Renard II.2.4)

For a sheaf `F` of abelian groups of base the compact opens of a t.d. space `X`, there is an
abelian group `F_c(X)` containing a copy `F₁(U)` of every `F(U)`, increasing in `U`, whose union
is `F_c(X)`, such that restriction to `U ⊂ V` fixes `F₁(U)` and restriction to `V ∖ U` kills it
(II.2.4, Proposition). For the sheaf of locally constant functions, `F_c(X)` is the algebra
`𝒟(X)` of compactly supported locally constant functions, with `F₁(U)` the functions
supported in `U` (the Example after the Proposition).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace

namespace Langlands.Sheaf.Renard

universe u v

/-- Renard II.2.4, Proposition: let `X` be a t.d. space and `F` a sheaf of abelian groups of
base the compact opens `T_c`. There are an abelian group `F_c(X)`, subgroups `F₁(U)` for
`U ∈ T_c` and additive isomorphisms `φ_U : F(U) ≃ F₁(U)` (so that `F₁`, with the transported
restrictions, is a sheaf isomorphic to `F`) such that
2. `F₁(U) ⊂ F₁(V)` for `U ⊂ V` in `T_c`;
3. for `U ⊂ V` in `T_c` and `f ∈ F₁(U)`, the restriction of `f` to `U` is `f` and its
   restriction to `V ∖ U` is `0`;
4. `F_c(X)` is the union of the `F₁(U)`. -/
def CompactOpenSheafCharacterizationStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)
    (F : BasisSheaf.{u, v} (ProjectorBasisSheaf.compactOpenBasis hX)),
    ∃ (Fc : Type (max u v)) (_ : AddCommGroup Fc)
      (S : BasisOpen (ProjectorBasisSheaf.compactOpenBasis hX) → AddSubgroup Fc)
      (φ : ∀ U, Sections F.obj.obj U ≃+ S U),
      (∀ U V : BasisOpen (ProjectorBasisSheaf.compactOpenBasis hX), U.obj ≤ V.obj → S U ≤ S V) ∧
      (∀ y : Fc, ∃ U, y ∈ S U) ∧
      (∀ (U V : BasisOpen (ProjectorBasisSheaf.compactOpenBasis hX)) (hUV : U.obj ≤ V.obj)
          (y : Fc), y ∈ S U → ∀ hyV : y ∈ S V,
          ((φ U (restriction F.obj.obj hUV ((φ V).symm ⟨y, hyV⟩)) : S U) : Fc) = y) ∧
      ∀ (U V W : BasisOpen (ProjectorBasisSheaf.compactOpenBasis hX)) (hWV : W.obj ≤ V.obj),
        U.obj ≤ V.obj → ((W.obj : Set X) = (V.obj : Set X) \ (U.obj : Set X)) →
        ∀ (y : Fc), y ∈ S U → ∀ hyV : y ∈ S V,
          restriction F.obj.obj hWV ((φ V).symm ⟨y, hyV⟩) = 0

/-- Renard II.2.4, Example: for the sheaf `𝒞^∞_X` of locally constant complex functions on a
t.d. space `X`, the group of the Proposition is the algebra `𝒟(X)` of compactly supported
locally constant functions. The data can be taken with `F₁(U)` the functions supported in `U`
and `φ_U` the extension by zero, and they satisfy the four properties of the Proposition. -/
def LocallyConstantCompactSectionsStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X),
    let B := ProjectorBasisSheaf.compactOpenBasis hX
    let F := LocallyConstantScalar.basisSheaf B ℂ
    ∃ (S : BasisOpen B → AddSubgroup (HarmonicAnalysis.PointwiseTestAlgebra.Carrier X))
      (φ : ∀ U, Sections F.obj.obj U ≃+ S U),
      (∀ (U : BasisOpen B) (f : HarmonicAnalysis.PointwiseTestAlgebra.Carrier X),
        f ∈ S U ↔ Function.support f ⊆ (U.obj : Set X)) ∧
      (∀ (U : BasisOpen B) (s : Sections F.obj.obj U) (x : X) (hx : x ∈ U.obj),
        ((φ U s : S U) : HarmonicAnalysis.PointwiseTestAlgebra.Carrier X) x =
          (show LocallyConstant U.obj ℂ from s) ⟨x, hx⟩) ∧
      (∀ U V : BasisOpen B, U.obj ≤ V.obj → S U ≤ S V) ∧
      (∀ y : HarmonicAnalysis.PointwiseTestAlgebra.Carrier X, ∃ U, y ∈ S U) ∧
      (∀ (U V : BasisOpen B) (hUV : U.obj ≤ V.obj)
          (y : HarmonicAnalysis.PointwiseTestAlgebra.Carrier X), y ∈ S U → ∀ hyV : y ∈ S V,
          ((φ U (restriction F.obj.obj hUV ((φ V).symm ⟨y, hyV⟩)) : S U) :
            HarmonicAnalysis.PointwiseTestAlgebra.Carrier X) = y) ∧
      ∀ (U V W : BasisOpen B) (hWV : W.obj ≤ V.obj),
        U.obj ≤ V.obj → ((W.obj : Set X) = (V.obj : Set X) \ (U.obj : Set X)) →
        ∀ (y : HarmonicAnalysis.PointwiseTestAlgebra.Carrier X), y ∈ S U → ∀ hyV : y ∈ S V,
          restriction F.obj.obj hWV ((φ V).symm ⟨y, hyV⟩) = 0

/-- Renard II.2.4, Example: the algebra `𝒟(X)` has a unit exactly when the t.d. space `X` is
compact (the unit is then the constant function `1 = χ_X` and `𝒟(X) = 𝒞^∞(X)`). -/
def PointwiseTestAlgebraUnitalIffCompactStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], Langlands.Topology.IsLocallyProfinite X →
    ((∃ e : HarmonicAnalysis.PointwiseTestAlgebra.Carrier X,
        ∀ f, e * f = f ∧ f * e = f) ↔ CompactSpace X)

end Langlands.Sheaf.Renard
