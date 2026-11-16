import Langlands.AlgebraicGeometry.Picard.PresheafLineBundle

/-! # Universal line bundles under changes of presheaf and representer -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PresheafLineBundle

variable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type v}
    (L : PresheafLineBundle F)

/-- Reindexing and transport of representing data evaluate the same family. -/
@[simp]
theorem universal_reindex_ofIso {M : Over S} (e : G.RepresentableBy M) (φ : G ≅ F) :
    (L.reindex φ.hom).universal e = L.universal (e.ofIso φ) := rfl

/-- Transporting a representation and reindexing back preserves its universal
line bundle by the inverse law of the presheaf isomorphism. -/
def universalOfIso {M : Over S} (e : F.RepresentableBy M) (φ : F ≅ G) :
    (L.reindex φ.inv).universal (e.ofIso φ) ≅ L.universal e :=
  eqToIso (congrArg (L.bundle M) (by simp [Functor.RepresentableBy.ofIso]))

/-- The map between supplied representers induced by a natural transformation
pulls back the universal line bundle to that of the reindexed bundle. -/
def universalReindexIso {M N : Over S} (e : F.RepresentableBy M)
    (d : G.RepresentableBy N) (φ : G ⟶ F) :
    (LineBundle.pullback
        (e.homEquiv.symm (φ.app (op N) (d.homEquiv (𝟙 N)))).left).obj
        (L.universal e) ≅ (L.reindex φ).universal d :=
  L.universalPullbackIso e _ ≪≫
    eqToIso (congrArg (L.bundle N) (e.homEquiv.apply_symm_apply _))

/-- The canonical isomorphism between supplied representers classifies their
same universal family. -/
@[simp]
theorem homEquiv_uniqueUpToIso {M N : Over S} (e : F.RepresentableBy M)
    (d : F.RepresentableBy N) :
    d.homEquiv (e.uniqueUpToIso d).hom = e.homEquiv (𝟙 M) := by
  change d.homEquiv (d.homEquiv.symm (e.homEquiv (𝟙 M))) = _
  exact d.homEquiv.apply_symm_apply _

/-- The universal bundles on two supplied representers agree after pullback
along their canonical representing isomorphism. -/
def universalCompareIso {M N : Over S} (e : F.RepresentableBy M)
    (d : F.RepresentableBy N) :
    (LineBundle.pullback (e.uniqueUpToIso d).hom.left).obj
        (L.universal d) ≅ L.universal e :=
  L.universalPullbackIso d (e.uniqueUpToIso d).hom ≪≫
    eqToIso (congrArg (L.bundle M) (homEquiv_uniqueUpToIso e d))

end Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
