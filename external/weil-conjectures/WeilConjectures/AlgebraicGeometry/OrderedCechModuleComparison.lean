/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleRetraction
import WeilConjectures.AlgebraicGeometry.OrderedCechModuleKernelNullHomotopic

/-! # Ordered versus usual Čech complexes of module sheaves

Source: Stacks Project, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A complex with the ordered section formulas is homotopy equivalent to the direct
image of any locally linear usual Čech presentation. No cover, affine, flatness or
quasi-coherence hypothesis is needed.
Source: Stacks Project, Tags 01FJ, 01FK and 01FM, the two sorting homotopies.
(blueprint: lem-pc-ordered-cech-module-comparison).

Proof: On an open B of T', evaluate the usual presentation on f' inverse image B.
Use e to identify the cochains with all tuples and a to identify the other complex
with strictly increasing tuples. Categorical products of opens identify with finite
intersections; replace ULift indices by their underlying Fin indices. Restriction
from all tuples to increasing tuples commutes with the differential by hd and ha.
Signed sorting, zero on repeated indices, gives the reverse cochain map. Their
ordered composite is the identity. For the other composite, stably sort the entries of
an output p-tuple by a
permutation sigma. Let sigma_a list its first a sorted positions and then the remaining
positions in their original order. The first homotopy evaluates a (p+1)-cochain on
sigma(0), ..., sigma(a), sigma_a(a), ..., sigma_a(p), summed over a with coefficient
(-1)^a sign(sigma_a), using the unique isomorphisms between equal intersections.
In dh + hd, deleting an entry away from the junction pairs with the same deletion
in the adjacent summand, with opposite sign. The endpoint terms give identity minus
signed stable sorting. Thus this retracts onto semi-alternating cochains, identified
with cochains on nondecreasing tuples. On such a tuple the second homotopy is zero
if it is strictly increasing; otherwise, at the first equality in position a, repeat
that entry with coefficient (-1)^a. Deletions before and after this repeated entry
cancel with the corresponding terms in hd, leaving identity minus extension by zero
from strictly increasing tuples. Composing these retractions gives a homotopy from
the full-complex composite to identity. The zero homotopy gives the ordered-complex
identity. These formulas use only restrictions, finite sums and integer signs. Consequently
they commute with restriction of B by hn and the naturality of e.
The local scalar identities hl and hlinear make all these maps and homotopies
O_T'(B)-linear, so they assemble into morphisms and homotopies of module sheaves.
Extend the usual complex by zero to integer degrees. K has zero negative terms by hK,
so the degree identifications and homotopies extend over those terms uniquely. For
r = 0 every product has empty index set, and these are the unique maps between zero
objects. The argument is independent of any covering or augmentation. -/
theorem orderedCech_module_comparison {X' T' : Scheme.{u}} (f' : X' ⟶ T')
    (M : X'.Modules) {r : ℕ} (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (K : CochainComplex T'.Modules ℤ) (hK : K.IsStrictlyGE 0)
    (a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)))
    (hn : ∀ (p : ℕ) {B C : T'.Opens} (i : B ⟶ C)
        (s : Γ(K.X (p : ℤ), C)) (t : Fin (p + 1) ↪o Fin r),
      a p B ((K.X (p : ℤ)).presheaf.map i.op s) t =
        M.presheaf.map (homOfLE (inf_le_inf le_rfl
          ((TopologicalSpace.Opens.map f'.base).map i).le)).op (a p C s t))
    (hl : ∀ (p : ℕ) (B : T'.Opens) (b : Γ(T', B))
        (s : Γ(K.X (p : ℤ), B)) (t : Fin (p + 1) ↪o Fin r),
      a p B (b • s) t =
        X'.presheaf.map (homOfLE (show
          alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B
            from inf_le_right)).op (f'.app B b) • a p B s t)
    (ha : ∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
        (t : Fin (p + 2) ↪o Fin r),
      a (p + 1) B ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          M.presheaf.map (homOfLE (inf_le_inf
            (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
              (a p B s ((Fin.succAboveOrderEmb j).trans t)))
    (D : CochainComplex X'.Modules ℕ)
    (e : ∀ p : ℕ, (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          (D.X p).val ≅
        ((cechComplexFunctor W₀).obj
          ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).X p)
    (hd : ∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor W₀).obj
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
              M.presheafModuleCat)).d p (p + 1))
    (hlinear : ∀ (p : ℕ) (y : Fin (p + 1) → ULift.{u} (Fin r)) (B : X'.Opens),
        let c : Γ(D.X p, B) → Γ(M, (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B) :=
          fun s ↦ ((e p).hom ≫ Pi.π (fun y : Fin (p + 1) → ULift.{u} (Fin r) ↦
            ((prod.functor (C := X'.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj
                M.presheafModuleCat).obj
                (op (∏ᶜ fun l ↦ W₀ (y l)))) y).app (op B) s
        ∀ (a : Γ(X', B)) (s : Γ(D.X p, B)),
          c (a • s) = X'.presheaf.map (prod.snd :
            (∏ᶜ fun l ↦ W₀ (y l)) ⨯ B ⟶ B).op a • c s) :
    Nonempty (HomotopyEquiv K
      ((((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
        ComplexShape.embeddingUpNat)) := by
  obtain ⟨rmap, imap, hi, hr⟩ :=
    orderedCech_module_retraction f' M W₀ K hK a hn hl ha D e hd hlinear
  let L := (((Modules.pushforward f').mapHomologicalComplex _).obj D).extend
    ComplexShape.embeddingUpNat
  let g : L ⟶ L := rmap ≫ imap - 𝟙 L
  have hgr : g ≫ rmap = 0 := by
    dsimp only [g]
    rw [Preadditive.sub_comp, Category.assoc, hi, Category.comp_id,
      Category.id_comp, sub_self]
  have hg : ∀ (p : ℕ) (B : T'.Opens) (s : Γ(L.X (p : ℤ), B))
      (t : Fin (p + 1) ↪o Fin r),
      orderedCechModuleCoordinate f' M W₀ D e p B t ((g.f (p : ℤ)).app B s) = 0 := by
    intro p B s t
    rw [← hr]
    have hz := congrArg (fun k : L ⟶ K ↦ (k.f (p : ℤ)).app B s) hgr
    have hzero : (rmap.f (p : ℤ)).app B ((g.f (p : ℤ)).app B s) = 0 := by
      simpa using hz
    rw [hzero, map_zero]
    rfl
  obtain ⟨h⟩ := orderedCech_module_kernel_nullHomotopic f' M W₀ D e hd hlinear g hg
  exact ⟨{
    hom := imap
    inv := rmap
    homotopyHomInvId := Homotopy.ofEq hi
    homotopyInvHomId := Homotopy.equivSubZero.symm h }⟩

end AlgebraicGeometry.Scheme.Modules
