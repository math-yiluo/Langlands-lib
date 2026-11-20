import Langlands.Geometry.FormalGroup.GlobalRationalHeight
import Langlands.Geometry.FormalGroup.RationalHeightBaseChange
import Langlands.Geometry.FormalGroup.RationalHeightComposition

/-! # Transport of the rank of an integral isogeny to its inverse section -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.RationalSectionIso

open CategoryTheory TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- A ranked integral isogeny gives its actual inverse section the negative signed height. -/
def inverseHeightPresentationOfHom {π : O} {q n H : ℕ}
    (e : RationalSectionIso F M N ⊤) (f : Hom M N)
    (he : e.hom = RationalSection.ofHom f ⊤) (hf : f.HasHeight q n)
    (hπ : algebraMap O F π ≠ 0) (hq : 0 < q) (hH : 0 < H)
    (hM : M.HasPiHeight π q H) (hN : N.HasPiHeight π q H) :
    {Q : RationalSection.HeightPresentation π q e.inv // Q.index = -(n : ℤ)} := by
  let P := RationalHom.GlobalHeightPresentation.ofIntegral (F := F) (π := π) f n hf
  let g := P.toScalarIsogenyPresentation.toQuasiIsogeny hπ hM.piDivisible hN.piDivisible
  have hg : g.hom = RationalHom.ofHom f := P.toScalarIsogenyPresentation.toQuasiIsogeny_hom _ _ _
  have hcompare : RationalSectionIso.ofQuasiIsogeny g ⊤ = e := by
    apply RationalSectionIso.ext
    change RationalSection.ofGlobalOn ⊤ g.hom = e.hom
    rw [hg, RationalSection.ofGlobalOn_ofHom, he]
  let inv := P.exists_inverse hπ hq hH hM hN g hg
  let Q := inv.choose
  let hinv : RationalSection.ofGlobalOn ⊤ g.inv = e.inv :=
    congrArg RationalSectionIso.inv hcompare
  refine ⟨hinv ▸ Q.onOpen hN ⊤, ?_⟩
  rw [RationalSection.HeightPresentation.index_cast, Q.index_onOpen, inv.choose_spec,
    RationalHom.GlobalHeightPresentation.index_ofIntegral]

/-- On the full spectrum, the inverse section has the constant negative rank height. -/
theorem hasHeightFunction_inv_ofHom {π : O} {q n H : ℕ}
    (e : RationalSectionIso F M N ⊤) (f : Hom M N)
    (he : e.hom = RationalSection.ofHom f ⊤) (hf : f.HasHeight q n)
    (hπ : algebraMap O F π ≠ 0) (hq : 0 < q) (hH : 0 < H)
    (hM : M.HasPiHeight π q H) (hN : N.HasPiHeight π q H) :
    RationalSection.HasHeightFunction π q e.inv (fun _ => -(n : ℤ)) := by
  let P := e.inverseHeightPresentationOfHom f he hf hπ hq hH hM hN
  intro x
  refine ⟨⊤, x.property, 𝟙 _, ?_⟩
  rw [RationalSection.restrict_id]
  exact ⟨P.val, fun _ => P.property.symm⟩

/-- Inverse precomposition subtracts the integral rank height, with the
same subtraction after coefficient pullback and integral conjugation. -/
theorem hasHeightFunction_transportIso_baseChange_comp_inv_ofHom
    {π : O} {q n H : ℕ} {υ σ' τ' : Type} [Finite υ] [Finite σ'] [Finite τ']
    {L : ModuleLaw O R υ}
    (e : RationalSectionIso F M N ⊤) (f : Hom M N)
    (he : e.hom = RationalSection.ofHom f ⊤) (hf : f.HasHeight q n)
    (hπ : algebraMap O F π ≠ 0) (hq : 2 ≤ q) (hH : 0 < H)
    (hM : M.HasPiHeight π q H) (hN : N.HasPiHeight π q H)
    {z : RationalSection F M L ⊤} {h : (⊤ : Opens (PrimeSpectrum R)) → ℤ}
    (hz : RationalSection.HasHeightFunction π q z h)
    {S : Type v} [CommRing S] [Algebra O S] (φ : R →ₐ[O] S)
    {N' : ModuleLaw O S σ'} {L' : ModuleLaw O S τ'}
    (a : Iso (N.map φ) N') (b : Iso (L.map φ) L') :
    RationalSection.HasHeightFunction π q
      (RationalSection.transportIso a b ((coefficientOpenMap φ).obj ⊤)
        (RationalSection.baseChange φ ⊤ (RationalSection.comp z e.inv)))
      (fun x => h (coefficientOpenPoint φ ⊤ x) - n) := by
  have hi := e.hasHeightFunction_inv_ofHom f he hf hπ (by omega) hH hM hN
  have hz' := RationalSection.HasHeightFunction.comp hq hN hM hz hi
  have hfun : (fun x => h (coefficientOpenPoint φ ⊤ x) - (n : ℤ)) =
      (fun x => -(n : ℤ) + h x) ∘ coefficientOpenPoint φ ⊤ := by
    funext x
    rw [Function.comp_apply, sub_eq_add_neg, add_comm]
  exact hfun.symm ▸ (hz'.baseChange φ).transportIso a b

end Langlands.FormalGroup.ModuleLaw.RationalSectionIso
