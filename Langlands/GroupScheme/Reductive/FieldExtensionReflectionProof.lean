import Langlands.GroupScheme.Reductive.FieldExtensionReflectionStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Connected reductivity and pseudo-reductivity under arbitrary field extension: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Pseudo-reductivity descends along every field extension: if `G_K` is pseudo-reductive,
so is `G`. -/
theorem IsPseudoReductive.of_fieldExtension
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsPseudoReductive
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    IsPseudoReductive G := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbSurjective
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQuasiCompact
  have hsmooth : Smooth G.X.hom := smooth_of_baseChange b G hG.smooth
  have hconn : ConnectedSpace G.X.left := connectedSpace_of_baseChange b G hG.connectedSpace
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := hG.isAffineHom
  have hAff : IsAffine ((GroupScheme.baseChange b).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj G).X.hom
  change IsAffine (pullback G.X.hom b) at hAff
  let : IsAffine G.X.left :=
    Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k K G.X.left G.X.hom hAff
  have haff : IsAffineHom G.X.hom := inferInstance
  exact ⟨hsmooth, haff, hconn,
    HasTrivialUnipotentRadical.of_fieldExtension hG.hasTrivialUnipotentRadical⟩

/-- Proof of `FieldExtensionReflectionStatement` (Milne, *Algebraic Groups* (2017),
Proposition 19.13; Conrad–Gabber–Prasad, proof of Proposition 1.1.9). -/
theorem fieldExtensionReflection : FieldExtensionReflectionStatement.{u} :=
  ⟨fun k K _ _ _ G =>
      ⟨connectedReductiveFieldExtensionStatement k K G, IsConnectedReductive.of_fieldExtension⟩,
    fun _ _ _ _ _ _ hG => IsPseudoReductive.of_fieldExtension hG⟩

end Langlands.GroupScheme
