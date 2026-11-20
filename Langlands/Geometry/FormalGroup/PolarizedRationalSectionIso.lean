import Langlands.Geometry.FormalGroup.PolarizedFramedAffineBaseChange
import Langlands.Geometry.FormalGroup.RationalTorsionSimilitudeComposition

/-! # Order-linear rational section isomorphisms preserving the polarization up to a scalar -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open TopologicalSpace _root_.AlgebraicGeometry

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {A : Type w} [Ring A] [Algebra O A]
variable {σ τ υ σ' τ' : Type} [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {L : ModuleLaw O R υ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {E : OrderAction A M} {G : OrderAction A N} {H : OrderAction A L}
variable {E' : OrderAction A M'} {G' : OrderAction A N'}
variable {U : Opens (PrimeSpectrum R)}

/-- An order-linear section intertwines the actual rational sections of the order endomorphisms. -/
def IsOrderLinear (E : OrderAction A M) (G : OrderAction A N) (f : RationalSection F M N U) : Prop :=
  ∀ b : A, comp f (ofHom (E.action b) U) = comp (ofHom (G.action b) U) f

namespace IsOrderLinear

variable {f : RationalSection F M N U} {g : RationalSection F N L U}

theorem id (E : OrderAction A M) (U : Opens (PrimeSpectrum R)) :
    IsOrderLinear E E (RationalSection.id (F := F) M U) := by
  intro b
  rw [id_comp, comp_id]

theorem ofHom (f : OrderAction.Hom E G) (U : Opens (PrimeSpectrum R)) :
    IsOrderLinear E G (RationalSection.ofHom (F := F) f.val U) := by
  intro b
  rw [comp_ofHom, comp_ofHom, f.commutes]

/-- Order-linearity is preserved by rational section composition. -/
theorem comp (hg : IsOrderLinear G H g) (hf : IsOrderLinear E G f) :
    IsOrderLinear E H (RationalSection.comp g f) := by
  intro b
  rw [comp_assoc, hf b, ← comp_assoc g, hg b, comp_assoc]

/-- The inverse section commutes with the order whenever its forward section does. -/
theorem inverse (e : RationalSectionIso F M N U) (hf : IsOrderLinear E G e.hom) :
    IsOrderLinear G E e.inv := by
  intro b
  calc
    RationalSection.comp e.inv (RationalSection.ofHom (G.action b) U) =
        RationalSection.comp e.inv (RationalSection.comp (RationalSection.ofHom (G.action b) U)
          (RationalSection.comp e.hom e.inv)) := by rw [e.hom_inv, comp_id]
    _ = RationalSection.comp e.inv (RationalSection.comp
        (RationalSection.comp (RationalSection.ofHom (G.action b) U) e.hom) e.inv) := by
      rw [comp_assoc]
    _ = RationalSection.comp (RationalSection.ofHom (E.action b) U) e.inv := by
      rw [← hf b, comp_assoc, ← comp_assoc e.inv, e.inv_hom, id_comp]

theorem baseChange (hf : IsOrderLinear E G f) (φ : R →ₐ[O] S) :
    IsOrderLinear (E.map φ) (G.map φ) (RationalSection.baseChange φ U f) := by
  intro b
  have h := congrArg (RationalSection.baseChange φ U) (hf b)
  simpa only [RationalSection.baseChange_comp, baseChange_ofHom, OrderAction.map_action] using h

/-- Conjugation by integral order-linear isomorphisms preserves order-linearity. -/
theorem transportIso (hf : IsOrderLinear E G f) (a : OrderAction.Iso E E')
    (b : OrderAction.Iso G G') :
    IsOrderLinear E' G' (RationalSection.transportIso a.toModuleIso b.toModuleIso U f) := by
  intro d
  have h := congrArg (RationalSection.transportIso a.toModuleIso b.toModuleIso U) (hf d)
  rw [RationalSection.transportIso_comp a.toModuleIso a.toModuleIso b.toModuleIso,
    RationalSection.transportIso_comp a.toModuleIso b.toModuleIso b.toModuleIso,
    transportIso_ofHom_of_commutes a.toModuleIso a.toModuleIso (a.hom.commutes d),
    transportIso_ofHom_of_commutes b.toModuleIso b.toModuleIso (b.hom.commutes d)] at h
  exact h

end IsOrderLinear

end Langlands.FormalGroup.ModuleLaw.RationalSection

namespace Langlands.FormalGroup.ModuleLaw.PolarizedOrderModule

open TopologicalSpace _root_.AlgebraicGeometry Langlands.Shimura

variable {prime : ℕ} [Fact prime.Prime]
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℤ_[prime] R] [Algebra ℤ_[prime] S]
variable {X Y Z : PolarizedOrderModule A star R (prime : ℤ_[prime])}
variable {X' Y' : PolarizedOrderModule A star R (prime : ℤ_[prime])}
variable {U : Opens (PrimeSpectrum R)}

/-- An actual rational order isomorphism whose two directions satisfy the
polarization equations with reciprocal multipliers. -/
structure RationalSimilitudeIso
    (X Y : PolarizedOrderModule A star R (prime : ℤ_[prime]))
    (U : Opens (PrimeSpectrum R)) where
  sectionIso : RationalSectionIso ℚ_[prime] X.law Y.law U
  orderLinear : RationalSection.IsOrderLinear X.order Y.order sectionIso.hom
  similitude : ∃ c : ℚ_[prime]ˣ,
    RationalSection.HasPadicTorsionSimilitude prime X.polarization Y.polarization sectionIso.hom c ∧
    RationalSection.HasPadicTorsionSimilitude prime Y.polarization X.polarization sectionIso.inv c⁻¹

namespace RationalSimilitudeIso

@[ext]
theorem ext {e f : RationalSimilitudeIso X Y U} (h : e.sectionIso.hom = f.sectionIso.hom) :
    e = f := by
  have hs := RationalSectionIso.ext h
  cases e
  cases f
  cases hs
  rfl

/-- An identity section is a similitude in both directions. -/
def refl (X : PolarizedOrderModule A star R (prime : ℤ_[prime])) (U : Opens (PrimeSpectrum R)) :
    RationalSimilitudeIso X X U where
  sectionIso := RationalSectionIso.refl X.law U
  orderLinear := RationalSection.IsOrderLinear.id (F := ℚ_[prime]) X.order U
  similitude := by
    have h := RationalSection.HasLocalTorsionSimilitude.id (p := (prime : ℤ_[prime]))
      (F := ℚ_[prime]) (k := ℚ_[prime]) X.polarization U
    exact ⟨1, h, (inv_one (G := ℚ_[prime]ˣ)).symm ▸ h⟩

/-- Reverse the actual rational section and its reciprocal multiplier. -/
def symm (e : RationalSimilitudeIso X Y U) : RationalSimilitudeIso Y X U where
  sectionIso := e.sectionIso.symm
  orderLinear := e.orderLinear.inverse e.sectionIso
  similitude := by
    obtain ⟨c, hf, hg⟩ := e.similitude
    exact ⟨c⁻¹, hg, (inv_inv c).symm ▸ hf⟩

/-- Compose the actual order-linear sections and multiply the rational multipliers. -/
def trans (e : RationalSimilitudeIso X Y U) (f : RationalSimilitudeIso Y Z U) :
    RationalSimilitudeIso X Z U where
  sectionIso := e.sectionIso.trans f.sectionIso
  orderLinear := f.orderLinear.comp e.orderLinear
  similitude := by
    obtain ⟨c, hc, hc'⟩ := e.similitude
    obtain ⟨d, hd, hd'⟩ := f.similitude
    exact ⟨c * d, hd.comp hc, (mul_inv_rev c d).symm ▸ hc'.comp hd'⟩

/-- Pull back the entire rational section isomorphism and its pairing equations. -/
def baseChange (e : RationalSimilitudeIso X Y U) (φ : R →ₐ[ℤ_[prime]] S) :
    RationalSimilitudeIso (X.map φ) (Y.map φ) ((coefficientOpenMap φ).obj U) where
  sectionIso := e.sectionIso.baseChange φ
  orderLinear := e.orderLinear.baseChange φ
  similitude := by
    obtain ⟨c, h, h'⟩ := e.similitude
    exact ⟨c, h.baseChange φ, h'.baseChange φ⟩

/-- Integral polarized isometries transport both actual rational multiplier equations. -/
def transportIso (e : RationalSimilitudeIso X Y U) (a : Iso X X') (b : Iso Y Y') :
    RationalSimilitudeIso X' Y' U where
  sectionIso := e.sectionIso.transportIso a.orderIso.toModuleIso b.orderIso.toModuleIso
  orderLinear := e.orderLinear.transportIso a.orderIso b.orderIso
  similitude := by
    obtain ⟨c, h, h'⟩ := e.similitude
    exact ⟨c, h.transportIso a.orderIso.toModuleIso b.orderIso.toModuleIso a.preserves b.preserves,
      h'.transportIso b.orderIso.toModuleIso a.orderIso.toModuleIso b.preserves a.preserves⟩

/-- Integral polarized order isometries give rational section similitudes with multiplier one. -/
def ofIso (e : Iso X Y) (U : Opens (PrimeSpectrum R)) : RationalSimilitudeIso X Y U where
  sectionIso := RationalSectionIso.ofIso e.orderIso.toModuleIso U
  orderLinear := RationalSection.IsOrderLinear.ofHom (F := ℚ_[prime]) e.orderIso.hom U
  similitude := by
    let g := e.orderIso.toModuleIso
    have h : RationalSection.HasPadicTorsionSimilitude prime X.polarization Y.polarization
        (RationalSection.ofHom (F := ℚ_[prime]) g.hom U) 1 :=
      RationalSection.HasLocalTorsionSimilitude.ofGlobalOn g.hom g.isIsogeny
        1 (map_one _) e.preserves
    have hinv : RationalSection.HasPadicTorsionSimilitude prime Y.polarization X.polarization
        (RationalSection.ofHom (F := ℚ_[prime]) g.inv U) 1 :=
      RationalSection.HasLocalTorsionSimilitude.ofGlobalOn g.inv g.symm.isIsogeny
        1 (map_one _) e.symm.preserves
    exact ⟨1, h, (inv_one (G := ℚ_[prime]ˣ)).symm ▸ hinv⟩

end RationalSimilitudeIso

end Langlands.FormalGroup.ModuleLaw.PolarizedOrderModule
