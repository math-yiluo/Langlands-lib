import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleComparison
import Langlands.AlgebraicGeometry.Picard.AffineBaseAmpleLocality

/-! # Ampleness of universal bundles from an open cover of an affine base -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace PresheafLineBundle

variable {S U : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    (L : PresheafLineBundle F)

/-- Restriction of a represented presheaf is represented by actual scheme pullback. -/
def baseChangeRepresentation (b : U ⟶ S) {M : Over S} (e : F.RepresentableBy M) :
    ((Over.map b).op ⋙ F).RepresentableBy ((Over.pullback b).obj M) where
  homEquiv := ((Over.mapPullbackAdj b).homEquiv _ M).symm.trans e.homEquiv
  homEquiv_comp a c := by
    dsimp
    rw [(Over.mapPullbackAdj b).homEquiv_naturality_left_symm, e.homEquiv_comp]

/-- Restriction of the coherent bundle evaluates to the actual pullback of
the original universal bundle. -/
def universalBaseChangeIso (b : U ⟶ S) {M : Over S} (e : F.RepresentableBy M) :
    (LineBundle.pullback (pullback.fst M.hom b)).obj (L.universal e) ≅
      (L.baseChange b).universal (baseChangeRepresentation b e) := by
  let a : (Over.map b).obj ((Over.pullback b).obj M) ⟶ M :=
    Over.homMk (pullback.fst M.hom b) pullback.condition
  refine L.universalPullbackIso e a ≪≫ eqToIso ?_
  apply congrArg (L.bundle ((Over.map b).obj ((Over.pullback b).obj M)))
  apply congrArg e.homEquiv
  ext
  simp [a, Over.mapPullbackAdj]

/-- Any supplied local representer gives the same universal bundle on the
actual pullback model, under its canonical representing isomorphism. -/
def universalBaseChangeCompareIso (b : U ⟶ S) {M : Over S}
    (e : F.RepresentableBy M) {N : Over U}
    (d : ((Over.map b).op ⋙ F).RepresentableBy N) :
    (LineBundle.pullback ((baseChangeRepresentation b e).uniqueUpToIso d).hom.left).obj
        ((L.baseChange b).universal d) ≅
      (LineBundle.pullback (pullback.fst M.hom b)).obj (L.universal e) :=
  (L.baseChange b).universalCompareIso (baseChangeRepresentation b e) d ≪≫
    (L.universalBaseChangeIso b e).symm

end PresheafLineBundle

namespace LineBundle

variable {X S : Scheme.{u}}

/-- Ampleness can be checked on pullbacks along an open cover of an affine
base when the total space is compact and quasi-separated. -/
theorem isAmple_of_affine_base_openCover
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S]
    (f : X ⟶ S) (L : LineBundle X) (𝒰 : Scheme.OpenCover.{u} S)
    (hL : ∀ i, ((LineBundle.pullback (pullback.fst f (𝒰.f i))).obj L).IsAmple) :
    L.IsAmple := by
  apply L.isAmple_of_affine_base_neighbourhoods f
  intro s
  let i := 𝒰.idx s
  let j := 𝒰.f i
  let V := f ⁻¹ᵁ j.opensRange
  let e : V.toScheme ≅ Limits.pullback f j :=
    IsOpenImmersion.isoOfRangeEq V.ι (pullback.fst f j) (by
      simpa [V] using (IsOpenImmersion.range_pullbackFst j f).symm)
  have ha := (hL i).pullback_of_isAffineHom e.hom
  have hc : e.hom ≫ pullback.fst f j = V.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine ⟨j.opensRange, ?_, ?_⟩
  · exact 𝒰.covers s
  · exact ha.of_iso ((Scheme.Modules.pullbackComp e.hom (pullback.fst f j)).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr hc).app L.obj)

end LineBundle

namespace PresheafLineBundle

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}
    (L : PresheafLineBundle F)

/-- An ample universal bundle on each supplied local representer gives an
ample universal bundle on a proper global representer over an affine base. -/
theorem isAmple_universal_of_affine_openCover [IsAffine S]
    {M : Over S} (e : F.RepresentableBy M) [IsProper M.hom]
    (𝒰 : Scheme.OpenCover.{u} S) (N : ∀ i, Over (𝒰.X i))
    (d : ∀ i, ((Over.map (𝒰.f i)).op ⋙ F).RepresentableBy (N i))
    (hL : ∀ i, ((L.baseChange (𝒰.f i)).universal (d i)).IsAmple) :
    (L.universal e).IsAmple := by
  let : CompactSpace M.left := QuasiCompact.compactSpace_of_compactSpace M.hom
  let : QuasiSeparatedSpace M.left := quasiSeparatedSpace_of_quasiSeparated M.hom
  apply (L.universal e).isAmple_of_affine_base_openCover M.hom 𝒰
  intro i
  let c := (baseChangeRepresentation (𝒰.f i) e).uniqueUpToIso (d i)
  exact ((hL i).pullback_of_isAffineHom c.hom.left).of_iso
    ((LineBundle.forget _).mapIso (L.universalBaseChangeCompareIso (𝒰.f i) e (d i)))

end PresheafLineBundle

end Langlands.AlgebraicGeometry.Picard
