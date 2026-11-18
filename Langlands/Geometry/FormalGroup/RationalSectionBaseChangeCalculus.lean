import Langlands.Geometry.FormalGroup.RationalSectionBaseChange
import Langlands.Geometry.FormalGroup.RationalSectionIso

/-! # Coefficient pullback of section composition, inverses and local isogenies -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem eq_of_local_lifts {X : TopCat.{v}}
    {A B : TopCat.Presheaf (Type v) X} (e : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e]
    (H : TopCat.Sheaf (Type v) X) {U : Opens X} (b : B.obj (op U))
    (s t : H.obj.obj (op U))
    (h : ∀ (V : Opens X) (i : V ⟶ U) (a : A.obj (op V)),
      e.app (op V) a = B.map i.op b → H.obj.map i.op s = H.obj.map i.op t) : s = t := by
  have hs : Presieve.IsSheaf (Opens.grothendieckTopology X) H.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp H.property
  exact (hs.isSeparated _ (Presheaf.imageSieve_mem _ e b)).ext
    (fun V i hi => h V i hi.choose hi.choose_spec)

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

namespace RationalSection

/-- Actual coefficient pullback preserves section identities. -/
@[simp]
theorem baseChange_id (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    baseChange φ U (id (F := F) M U) = id (M.map φ) ((coefficientOpenMap φ).obj U) := by
  rw [← ofGlobalOn_id, baseChange_ofGlobalOn, RationalHom.map_id, ofGlobalOn_id]

/-- Actual coefficient pullback preserves composition of arbitrary sheaf sections. -/
@[simp]
theorem baseChange_comp (φ : R →ₐ[O] S) {U : Opens (PrimeSpectrum R)}
    (g : RationalSection F N P U) (f : RationalSection F M N U) :
    baseChange φ U (comp g f) = comp (baseChange φ U g) (baseChange φ U f) := by
  apply eq_of_local_lifts
    (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N))
    ((TopCat.Sheaf.pushforward (Type v) (coefficientSpectrumMap φ)).obj
      (rationalHomTypeSheaf F (M.map φ) (P.map φ))) (g, f)
  rintro V i ⟨g', f'⟩ heq
  change (ofRational V g', ofRational V f') = (restrict i g, restrict i f) at heq
  obtain ⟨hg, hf⟩ := Prod.mk.inj heq
  change restrict ((coefficientOpenMap φ).map i) (baseChange φ U (comp g f)) =
    restrict ((coefficientOpenMap φ).map i) (comp (baseChange φ U g) (baseChange φ U f))
  rw [restrict_baseChange, restrict_comp_hom, restrict_comp_hom,
    restrict_baseChange, restrict_baseChange, ← hg, ← hf]
  erw [comp_ofRational, baseChange_ofRational, baseChange_ofRational,
    baseChange_ofRational, comp_ofRational]
  change ofRational _ (RationalHom.mapSquareLinear _ _ _ _ _ (RationalHom.comp g' f')) =
    ofRational _ (RationalHom.comp
      (RationalHom.mapSquareLinear _ _ _ _ _ g') (RationalHom.mapSquareLinear _ _ _ _ _ f'))
  erw [RationalHom.mapSquareLinear_hom_comp]

/-- Integral numerators pull back through the actual coefficient square. -/
@[simp]
theorem baseChange_ofIntegral (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R))
    (f : OpenIntegralHom M N U) :
    baseChange φ U (ofIntegral U f : RationalSection F M N U) =
      ofIntegral ((coefficientOpenMap φ).obj U) (Hom.openBaseChange φ U f) := by
  change baseChange φ U (ofRational U (RationalHom.ofHom f)) = _
  erw [baseChange_ofRational]
  change ofRational _ (RationalHom.mapSquareLinear _ _ _ _ _ (RationalHom.ofHom f)) = _
  rw [RationalHom.mapSquareLinear_ofHom]
  rfl

end RationalSection

namespace Hom

/-- The actual finite-kernel and lifting conditions survive the open coefficient square. -/
theorem IsIsogeny.openBaseChange {U : Opens (PrimeSpectrum R)}
    {f : OpenIntegralHom M N U} (hf : f.IsIsogeny) (φ : R →ₐ[O] S) :
    (Hom.openBaseChange φ U f).IsIsogeny := by
  let α := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))
  let β := coefficientSectionMap φ U
  let δ := IsScalarTower.toAlgHom O S
    ((coefficientStructurePresheaf S).obj (op ((coefficientOpenMap φ).obj U)))
  let h := coefficientSectionMap_structural φ U
  apply isIsogeny_of_isoSquare (f.map β) (Hom.openBaseChange φ U f)
    (mapSquareIso M α β φ δ h) (mapSquareIso N α β φ δ h)
  · change ((mapSquareIso N α β φ δ h).hom.comp
      ((f.map β).comp (mapSquareIso M α β φ δ h).inv)).comp
        (mapSquareIso M α β φ δ h).hom = _
    rw [Hom.comp_assoc, Hom.comp_assoc, Iso.inv_hom, Hom.comp_id]
  · exact hf.map β

end Hom

namespace RationalSection

/-- Pull back the actual neighbourhood and numerator while keeping its scalar exponent. -/
theorem IsLocallyScalarIsogeny.baseChange {π : O} {U : Opens (PrimeSpectrum R)}
    {z : RationalSection F M N U} (hz : IsLocallyScalarIsogeny π z)
    (φ : R →ₐ[O] S) : IsLocallyScalarIsogeny π (RationalSection.baseChange φ U z) := by
  intro x hx
  obtain ⟨V, hxV, i, n, f, hf, heq⟩ := hz ((coefficientSpectrumMap φ) x) hx
  refine ⟨(coefficientOpenMap φ).obj V, hxV, (coefficientOpenMap φ).map i, n,
    Hom.openBaseChange φ V f, hf.openBaseChange φ, ?_⟩
  have h := congrArg (RationalSection.baseChange φ V) heq
  simpa only [map_smul, ← RationalSection.restrict_baseChange,
    RationalSection.baseChange_ofIntegral] using h

end RationalSection

namespace LocalQuasiIsogeny

/-- Coefficient pullback of an actual local quasi-isogeny on any open. -/
def baseChange {π : O} {U : Opens (PrimeSpectrum R)}
    (z : LocalQuasiIsogeny F π M N U) (φ : R →ₐ[O] S) :
    LocalQuasiIsogeny F π (M.map φ) (N.map φ) ((coefficientOpenMap φ).obj U) where
  scalar_ne_zero := z.scalar_ne_zero
  source_divisible := z.source_divisible.map φ
  target_divisible := z.target_divisible.map φ
  val := RationalSection.baseChange φ U z.val
  isLocal := z.isLocal.baseChange φ

@[simp]
theorem restrict_baseChange {π : O} {U V : Opens (PrimeSpectrum R)}
    (z : LocalQuasiIsogeny F π M N U) (φ : R →ₐ[O] S) (i : V ⟶ U) :
    (z.baseChange φ).restrict ((coefficientOpenMap φ).map i) = (z.restrict i).baseChange φ := by
  apply ext
  exact RationalSection.restrict_baseChange φ i z.val

end LocalQuasiIsogeny

namespace RationalSectionIso

/-- Pull back the two actual inverse sections and their two inverse equations. -/
def baseChange {U : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (φ : R →ₐ[O] S) :
    RationalSectionIso F (M.map φ) (N.map φ) ((coefficientOpenMap φ).obj U) where
  hom := RationalSection.baseChange φ U e.hom
  inv := RationalSection.baseChange φ U e.inv
  inv_hom := by
    rw [← RationalSection.baseChange_comp, e.inv_hom, RationalSection.baseChange_id]
  hom_inv := by
    rw [← RationalSection.baseChange_comp, e.hom_inv, RationalSection.baseChange_id]

@[simp]
theorem restrict_baseChange {U V : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (φ : R →ₐ[O] S) (i : V ⟶ U) :
    (e.baseChange φ).restrict ((coefficientOpenMap φ).map i) = (e.restrict i).baseChange φ := by
  apply ext
  exact RationalSection.restrict_baseChange φ i e.hom

@[simp]
theorem baseChange_refl (φ : R →ₐ[O] S) (M : ModuleLaw O R σ)
    (U : Opens (PrimeSpectrum R)) :
    (refl (F := F) M U).baseChange φ = refl (M.map φ) ((coefficientOpenMap φ).obj U) := by
  apply ext
  exact RationalSection.baseChange_id φ U

@[simp]
theorem baseChange_symm {U : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (φ : R →ₐ[O] S) :
    e.symm.baseChange φ = (e.baseChange φ).symm := rfl

@[simp]
theorem baseChange_trans {U : Opens (PrimeSpectrum R)}
    (e : RationalSectionIso F M N U) (f : RationalSectionIso F N P U) (φ : R →ₐ[O] S) :
    (e.trans f).baseChange φ = (e.baseChange φ).trans (f.baseChange φ) := by
  apply ext
  exact RationalSection.baseChange_comp φ f.hom e.hom

@[simp]
theorem baseChange_ofIso (e : Iso M N) (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    (ofIso (F := F) e U).baseChange φ = ofIso (e.map φ) ((coefficientOpenMap φ).obj U) := by
  apply ext
  exact RationalSection.baseChange_ofHom φ U e.hom

@[simp]
theorem baseChange_ofQuasiIsogeny [IsDomain O] [IsFractionRing O F]
    (e : QuasiIsogeny F M N) (φ : R →ₐ[O] S) (U : Opens (PrimeSpectrum R)) :
    (ofQuasiIsogeny e U).baseChange φ =
      ofQuasiIsogeny (e.map φ) ((coefficientOpenMap φ).obj U) := by
  apply ext
  exact RationalSection.baseChange_ofGlobalOn φ U e.hom

end RationalSectionIso
end Langlands.FormalGroup.ModuleLaw
