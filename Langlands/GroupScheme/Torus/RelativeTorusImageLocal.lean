import Langlands.GroupScheme.Torus.SplitTorusImageLocal
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Étale-local closed factorizations of relative torus maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SplitTorusImageLocal

/-- Reindex a local factorization along the comparison for successive base changes. -/
def Factorization.ofComp {S U V : Scheme.{u}} {T G : GroupScheme S} {f : T ⟶ G}
    (a : U ⟶ S) (b : V ⟶ U)
    (D : Factorization ((baseChange b).map ((baseChange a).map f))) :
    Factorization ((baseChange (b ≫ a)).map f) := by
  let eT := baseChangeCompIso a b T
  let eG := baseChangeCompIso a b G
  have : IsIso eT.hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget V).mapIso ((Grp.forget _).mapIso eT)).hom)
  have : IsIso eG.inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget V).mapIso ((Grp.forget _).mapIso eG)).inv)
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosed
  have : Flat D.projection.hom.hom.left := D.flat
  have : Surjective D.projection.hom.hom.left := D.surjective
  refine ⟨D.image, eT.hom ≫ D.projection, D.inclusion ≫ eG.inv, D.isSplit, ?_, ?_, ?_, ?_⟩
  · change IsClosedImmersion (D.inclusion.hom.hom.left ≫ eG.inv.hom.hom.left)
    infer_instance
  · change Flat (eT.hom.hom.hom.left ≫ D.projection.hom.hom.left)
    infer_instance
  · change Surjective (eT.hom.hom.hom.left ≫ D.projection.hom.hom.left)
    infer_instance
  · rw [Category.assoc, ← Category.assoc D.projection, D.fac]
    change eT.hom ≫ (baseChange b).map ((baseChange a).map f) ≫ eG.inv = _
    rw [← Category.assoc, ← baseChangeCompIso_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

private theorem exists_away_cover {R : CommRingCat.{u}} {T G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T) (f : T ⟶ G) :
    ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec R),
      ∀ j : 𝒱.I₀, Nonempty (Factorization ((baseChange (𝒱.f j)).map f)) := by
  classical
  choose r hr _ hD using exists_away_factorization hT f
  let b (x : PrimeSpectrum R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (r x))))
  refine ⟨Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum R)
    (fun x => Spec (CommRingCat.of (Localization.Away (r x)))) b ?_ (fun _ => inferInstance), hD⟩
  intro x
  change PrimeSpectrum R at x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r x)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r x)) (r x)]
    exact hr x
  obtain ⟨y, hy⟩ := hx
  exact ⟨x, y, hy⟩

/-- An étale cover of the base carries closed split-torus factorizations of an
actual map from a relative torus to an affine group of locally finite type. -/
theorem exists_etale_factorizations {S : Scheme.{u}} {T G : GroupScheme S}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : RelativeTorus.IsTorus T) (f : T ⟶ G) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ i : 𝒰.I₀, Nonempty (Factorization ((baseChange (𝒰.f i)).map f)) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hT
  let 𝒜 (i : 𝒰.I₀) : (𝒰.X i).Cover (Scheme.precoverage @Etale) :=
    (𝒰.X i).affineCover.changeProp (fun _ => inferInstance)
  let 𝒱 := 𝒰.bind 𝒜
  have hv (i : 𝒱.I₀) : IsSplitTorus ((baseChange (𝒱.f i)).obj T) := by
    rcases i with ⟨i, j⟩
    exact IsSplitTorus.of_iso (baseChangeCompIso (𝒰.f i) ((𝒜 i).f j) T)
      ((h𝒰 i).baseChange ((𝒜 i).f j))
  have hlocal (i : 𝒱.I₀) :
      ∃ 𝒲 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (𝒱.X i),
        ∀ j : 𝒲.I₀, Nonempty (Factorization
          ((baseChange (𝒲.f j)).map ((baseChange (𝒱.f i)).map f))) := by
    have : IsAffineHom ((baseChange (𝒱.f i)).obj G).X.hom :=
      MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom G.X.hom)
    have : LocallyOfFiniteType ((baseChange (𝒱.f i)).obj G).X.hom :=
      MorphismProperty.pullback_snd _ _ (inferInstance : LocallyOfFiniteType G.X.hom)
    rcases i with ⟨i, j⟩
    exact exists_away_cover (hv ⟨i, j⟩) ((baseChange (𝒱.f ⟨i, j⟩)).map f)
  choose 𝒲 h𝒲 using hlocal
  refine ⟨𝒱.bind 𝒲, ?_⟩
  rintro ⟨i, j⟩
  exact (h𝒲 i j).map (Factorization.ofComp (𝒱.f i) ((𝒲 i).f j))

end Langlands.GroupScheme.SplitTorusImageLocal
