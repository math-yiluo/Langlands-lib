import Langlands.CategoryTheory.RationalizationDenominators
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Equivariant integral representatives of rational isomorphisms -/

noncomputable section

open CategoryTheory Module

set_option autoImplicit false
set_option maxHeartbeats 800000

universe v u w z

namespace Langlands.Rationalization

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A finite family of equalities after rationalization has one nonzero integer
that makes all the equalities hold before rationalization. -/
theorem exists_common_zsmul_eq {X Y : C} {ι : Type w} [Finite ι]
    (f g : ι → (X ⟶ Y)) (h : ∀ i, ofHom (f i) = ofHom (g i)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ i, n • f i = n • g i := by
  classical
  let := Fintype.ofFinite ι
  choose n hn he using fun i => (ofHom_eq_iff_exists_zsmul_eq (f i) (g i)).mp (h i)
  refine ⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro i
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hq]
  simpa only [smul_smul, mul_comm] using congrArg (fun t => q • t) (he i)

namespace IntegralIsoData

variable {X Y : C} {e : of X ≅ of Y}

/-- Independently scale the two integral representatives and their denominators,
preserving both exact inverse-multiple identities. -/
def rescale (d : IntegralIsoData e) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) :
    IntegralIsoData e where
  homDenom := r * d.homDenom
  invDenom := s * d.invDenom
  homDenom_ne_zero := mul_ne_zero hr d.homDenom_ne_zero
  invDenom_ne_zero := mul_ne_zero hs d.invDenom_ne_zero
  hom := r • d.hom
  inv := s • d.inv
  ofHom_hom := by rw [map_zsmul, d.ofHom_hom, smul_smul]
  ofHom_inv := by rw [map_zsmul, d.ofHom_inv, smul_smul]
  hom_inv := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, d.hom_inv]
    simp only [smul_smul, mul_left_comm, mul_comm]
  inv_hom := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, d.inv_hom]
    simp only [smul_smul, mul_left_comm, mul_comm]

end IntegralIsoData

variable {O : Type w} [Ring O] {X Y : C}
    (a : O →+* CategoryTheory.End X) (a' : O →+* CategoryTheory.End Y)

/-- To intertwine two integral actions, it suffices to intertwine an integer basis. -/
theorem intertwines_of_basis {ι : Type z} (b : Basis ι ℤ O) (f : X ⟶ Y)
    (h : ∀ i, a (b i) ≫ f = f ≫ a' (b i)) :
    ∀ x : O, a x ≫ f = f ≫ a' x := by
  let l : O →ₗ[ℤ] (X ⟶ Y) :=
    ((CategoryTheory.Linear.comp (S := ℤ) X X Y).flip f).comp
      a.toAddMonoidHom.toIntLinearMap
  let r : O →ₗ[ℤ] (X ⟶ Y) :=
    ((CategoryTheory.Linear.comp (S := ℤ) X Y Y) f).comp
      a'.toAddMonoidHom.toIntLinearMap
  have hlr : l = r := b.ext h
  exact fun x => DFunLike.congr_fun hlr x

/-- Integral representatives of a rational isomorphism that exactly intertwine
both integral actions in both directions. -/
structure EquivariantIntegralIsoData (e : of X ≅ of Y) extends IntegralIsoData e where
  hom_intertwines : ∀ x : O, a x ≫ hom = hom ≫ a' x
  inv_intertwines : ∀ x : O, a' x ≫ inv = inv ≫ a x

/-- Exact equivariant integral representatives exist for any rational
isomorphism intertwining actions of a ring with a finite integer basis. -/
theorem nonempty_equivariantIntegralIsoData {ι : Type z} [Finite ι] (b : Basis ι ℤ O)
    (e : of X ≅ of Y)
    (he : ∀ x : O, (ofHom (a x) : of X ⟶ of X) ≫ e.hom =
      e.hom ≫ ofHom (a' x)) :
    Nonempty (EquivariantIntegralIsoData a a' e) := by
  let d := integralIsoData e
  have hinv (x : O) : (ofHom (a' x) : of Y ⟶ of Y) ≫ e.inv =
      e.inv ≫ ofHom (a x) := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← he x]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  have hhom (x : O) : ofHom (a x ≫ d.hom) = ofHom (d.hom ≫ a' x) := by
    rw [ofHom_comp, ofHom_comp, d.ofHom_hom]
    change (ofHom (a x) : of X ⟶ of X) ≫ (d.homDenom • e.hom) =
      (d.homDenom • e.hom) ≫ ofHom (a' x)
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, he x]
  have hinv' (x : O) : ofHom (a' x ≫ d.inv) = ofHom (d.inv ≫ a x) := by
    rw [ofHom_comp, ofHom_comp, d.ofHom_inv]
    change (ofHom (a' x) : of Y ⟶ of Y) ≫ (d.invDenom • e.inv) =
      (d.invDenom • e.inv) ≫ ofHom (a x)
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, hinv x]
  obtain ⟨r, hr, hrf⟩ := exists_common_zsmul_eq
    (fun i => a (b i) ≫ d.hom) (fun i => d.hom ≫ a' (b i)) (fun i => hhom (b i))
  obtain ⟨s, hs, hsg⟩ := exists_common_zsmul_eq
    (fun i => a' (b i) ≫ d.inv) (fun i => d.inv ≫ a (b i)) (fun i => hinv' (b i))
  refine ⟨{
    toIntegralIsoData := d.rescale r s hr hs
    hom_intertwines := intertwines_of_basis a a' b (r • d.hom) ?_
    inv_intertwines := intertwines_of_basis a' a b (s • d.inv) ?_ }⟩
  · intro i
    simpa only [Preadditive.comp_zsmul, Preadditive.zsmul_comp] using hrf i
  · intro i
    simpa only [Preadditive.comp_zsmul, Preadditive.zsmul_comp] using hsg i

/-- A choice from the proved existence of exactly equivariant integral maps. -/
def equivariantIntegralIsoData {ι : Type z} [Finite ι] (b : Basis ι ℤ O)
    (e : of X ≅ of Y)
    (he : ∀ x : O, (ofHom (a x) : of X ⟶ of X) ≫ e.hom =
      e.hom ≫ ofHom (a' x)) :
    EquivariantIntegralIsoData a a' e :=
  Classical.choice (nonempty_equivariantIntegralIsoData a a' b e he)

end Langlands.Rationalization
