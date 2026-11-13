import Langlands.GroupScheme.Reductive.DirectProductStatement
import Langlands.GroupScheme.Reductive.FiniteProducts
import Langlands.GroupScheme.Reductive.ProductCenter
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProduct
import Langlands.GroupScheme.Torus.Products

/-! # Direct products of pseudo-reductive, reductive and semisimple groups: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme

namespace DirectProduct

section Pair

variable {S : Scheme.{u}}

/-- The two-member family `G, H`, indexed by `PUnit ⊕ PUnit`. -/
abbrev pairFamily (G H : GroupScheme S) : PUnit.{u + 1} ⊕ PUnit.{u + 1} → GroupScheme S :=
  sumGroupFamily (fun _ : PUnit.{u + 1} => G) (fun _ : PUnit.{u + 1} => H)

/-- The binary product `G ⊗ H` is the finite product of the two-member family. -/
def tensorIsoPi (G H : GroupScheme S) : G ⊗ H ≅ pi (pairFamily G H) :=
  ((productUniqueIso (fun _ : PUnit.{u + 1} => G)).symm ⊗ᵢ
    (productUniqueIso (fun _ : PUnit.{u + 1} => H)).symm) ≪≫
    finiteProductSumIso (fun _ : PUnit.{u + 1} => G) (fun _ : PUnit.{u + 1} => H)

end Pair

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Trivial ground-field unipotent radicals pass to the direct product of two affine
groups locally of finite type. -/
theorem hasTrivialUnipotentRadical_tensor
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (hG : HasTrivialUnipotentRadical G) (hH : HasTrivialUnipotentRadical H) :
    HasTrivialUnipotentRadical (G ⊗ H) := by
  have : ∀ x, IsAffineHom (pairFamily G H x).X.hom := by
    rintro (_ | _) <;> assumption
  have : ∀ x, LocallyOfFiniteType (pairFamily G H x).X.hom := by
    rintro (_ | _) <;> assumption
  exact HasTrivialUnipotentRadical.of_iso (tensorIsoPi G H)
    (HasTrivialUnipotentRadical.pi (pairFamily G H) (by rintro (_ | _) <;> assumption))

/-- The direct product of two pseudo-reductive groups is pseudo-reductive. -/
theorem isPseudoReductive_tensor (hG : IsPseudoReductive G) (hH : IsPseudoReductive H) :
    IsPseudoReductive (G ⊗ H) :=
  IsPseudoReductive.of_iso (tensorIsoPi G H)
    (isPseudoReductive_pi (pairFamily G H) (by rintro (_ | _) <;> assumption))

/-- The direct product of two connected reductive groups is connected reductive. -/
theorem isConnectedReductive_tensor (hG : IsConnectedReductive G)
    (hH : IsConnectedReductive H) : IsConnectedReductive (G ⊗ H) := by
  have hP := isPseudoReductive_tensor hG.isPseudoReductive hH.isPseudoReductive
  refine ⟨hP.smooth, hP.isAffineHom, hP.connectedSpace, ?_⟩
  have := hG.smooth
  have := hG.isAffineHom
  have := hH.smooth
  have := hH.isAffineHom
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom (toAlgebraicClosure k))
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X.hom := by
    change LocallyOfFiniteType (pullback.snd H.X.hom (toAlgebraicClosure k))
    infer_instance
  exact HasTrivialUnipotentRadical.of_iso (baseChangeTensorIso (toAlgebraicClosure k) G H)
    (hasTrivialUnipotentRadical_tensor hG.hasTrivialGeometricUnipotentRadical
      hH.hasTrivialGeometricUnipotentRadical)

/-- The direct product of two semisimple groups is semisimple. -/
theorem isSemisimple_tensor (hG : IsSemisimple G) (hH : IsSemisimple H) :
    IsSemisimple (G ⊗ H) :=
  ⟨isConnectedReductive_tensor hG.isConnectedReductive hH.isConnectedReductive,
    HasFiniteCenter.tensor hG.hasFiniteCenter hH.hasFiniteCenter⟩

end DirectProduct

/-- **Direct products** of pseudo-reductive, connected reductive and semisimple groups
over a field keep these properties. -/
theorem directProductReductive : DirectProductReductiveStatement.{u} := by
  intro k _ G H
  exact ⟨DirectProduct.isPseudoReductive_tensor, DirectProduct.isConnectedReductive_tensor,
    DirectProduct.isSemisimple_tensor⟩

end Langlands.GroupScheme
