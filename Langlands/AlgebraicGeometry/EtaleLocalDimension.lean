import Langlands.AlgebraicGeometry.SchemeLocalFiberDimension
import Langlands.AlgebraicGeometry.FlatOpenLocalDimension
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Actual local topological dimension under etale morphisms -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- A quasi-finite spectrum map cannot increase local topological dimension. -/
theorem topologicalKrullDimAt_le_comap_of_quasiFinite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] (q : PrimeSpectrum S) :
    topologicalKrullDimAt q ≤ topologicalKrullDimAt (q.comap (algebraMap R S)) := by
  let p := q.comap (algebraMap R S)
  obtain ⟨r, hr, hdim⟩ := exists_away_dimension_eq_at R p
  let s : S := algebraMap R S r
  have hs : s ∉ q.asIdeal := hr
  let Rr := Localization.Away r
  let Ss := Localization.Away s
  let ι : Rr →ₐ[R] Ss := Localization.awayMapₐ (Algebra.ofId R S) r
  let : Algebra Rr Ss := ι.toRingHom.toAlgebra
  have : IsScalarTower R Rr Ss := .of_algebraMap_eq' ι.comp_algebraMap.symm
  have : Algebra.QuasiFinite R Ss := .of_isLocalization (Submonoid.powers s)
  have : Algebra.QuasiFinite Rr Ss := .of_restrictScalars R Rr Ss
  let e := localizationAwayBasicOpenHomeomorph s
  let z := e.symm ⟨q, hs⟩
  have hz : PrimeSpectrum.comap (algebraMap S Ss) z = q :=
    congrArg Subtype.val (e.apply_symm_apply ⟨q, hs⟩)
  have hlocal : topologicalKrullDimAt z = topologicalKrullDimAt q :=
    (topologicalKrullDimAt_eq_of_isOpenEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding Ss s) z).trans
      (congrArg topologicalKrullDimAt hz)
  calc
    topologicalKrullDimAt q = topologicalKrullDimAt z := hlocal.symm
    _ ≤ topologicalKrullDim (PrimeSpectrum Ss) := topologicalKrullDimAt_le z
    _ = ringKrullDim Ss := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ ringKrullDim Rr := Langlands.AlgebraicGeometry.ringKrullDim_le_of_quasiFinite
    _ = topologicalKrullDimAt p := hdim

/-- A flat open quasi-finite spectrum map preserves local topological dimension. -/
theorem topologicalKrullDimAt_comap_eq_of_flat_quasiFinite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.QuasiFinite R S]
    (ho : IsOpenMap (PrimeSpectrum.comap (algebraMap R S))) (q : PrimeSpectrum S) :
    topologicalKrullDimAt q = topologicalKrullDimAt (q.comap (algebraMap R S)) :=
  le_antisymm (topologicalKrullDimAt_le_comap_of_quasiFinite R S q)
    (topologicalKrullDimAt_comap_le_of_flat_of_isOpenMap R S ho q)

/-- An etale morphism between affine schemes preserves local topological dimension. -/
theorem topologicalKrullDimAt_etale_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Etale f] (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  let R := Γ(Y, ⊤)
  let A := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : Module.Flat R A := f.flat_appTop
  have : Algebra.FinitePresentation R A :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) f inferInstance
  have : LocallyQuasiFinite f := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale f
  have : Algebra.QuasiFinite R A :=
    HasRingHomProperty.appTop (P := @LocallyQuasiFinite) f inferInstance
  have ho : IsOpenMap (PrimeSpectrum.comap (algebraMap R A)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have he : (X.isoSpec.hom x).comap (algebraMap R A) = Y.isoSpec.hom (f x) :=
    congrArg (fun k => k x) (Scheme.isoSpec_hom_naturality f)
  calc
    topologicalKrullDimAt x = topologicalKrullDimAt (X.isoSpec.hom x) :=
      topologicalKrullDimAt_eq_of_isOpenEmbedding X.isoSpec.hom.isOpenEmbedding x
    _ = topologicalKrullDimAt ((X.isoSpec.hom x).comap (algebraMap R A)) :=
      topologicalKrullDimAt_comap_eq_of_flat_quasiFinite R A ho (X.isoSpec.hom x)
    _ = topologicalKrullDimAt (Y.isoSpec.hom (f x)) := congrArg topologicalKrullDimAt he
    _ = topologicalKrullDimAt (f x) :=
      (topologicalKrullDimAt_eq_of_isOpenEmbedding Y.isoSpec.hom.isOpenEmbedding (f x)).symm

/-- Etale scheme morphisms preserve the actual dimension of open neighbourhoods
at every point, over arbitrary bases. -/
theorem topologicalKrullDimAt_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let φ := f.resLE U V hVU
  calc
    topologicalKrullDimAt x = topologicalKrullDimAt (⟨x, hxV⟩ : V) :=
      (topologicalKrullDimAt_open V ⟨x, hxV⟩).symm
    _ = topologicalKrullDimAt (φ ⟨x, hxV⟩) :=
      topologicalKrullDimAt_etale_affine φ ⟨x, hxV⟩
    _ = topologicalKrullDimAt (f x) := by
      simpa only [φ, Scheme.Hom.coe_resLE_apply] using
        topologicalKrullDimAt_open U (φ ⟨x, hxV⟩)

/-- Etale maps preserve pure dimension of schemes locally of finite type over a field. -/
theorem HasPureDimension.of_etale
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [Etale f] {d : ℕ} (h : HasPureDimension Y d) :
    HasPureDimension X d := by
  apply (hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType
    k X (f ≫ p) d).mpr
  intro x
  exact (topologicalKrullDimAt_etale f x).trans
    ((hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType k Y p d).mp h (f x))

/-- A surjective etale map tests pure dimension of a locally finite-type field scheme. -/
theorem hasPureDimension_etale_iff
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [Etale f] [Surjective f] (d : ℕ) :
    HasPureDimension X d ↔ HasPureDimension Y d := by
  refine ⟨?_, fun h => h.of_etale k p f⟩
  intro h
  apply (hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType k Y p d).mpr
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  exact (topologicalKrullDimAt_etale f x).symm.trans
    ((hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType
      k X (f ≫ p) d).mp h x)

/-- Local topological dimension is invariant under arbitrary etale scheme morphisms. -/
def EtaleLocalTopologicalDimensionStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [Etale f] (x : X),
    topologicalKrullDimAt x = topologicalKrullDimAt (f x)

/-- The complete universal local-dimension comparison. -/
theorem etaleLocalTopologicalDimension : EtaleLocalTopologicalDimensionStatement.{u} := by
  intro X Y f _ x
  exact topologicalKrullDimAt_etale f x

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
