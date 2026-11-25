/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SimplicialHomObjectExists
public import Mathlib.CategoryTheory.RepresentedBy

/-!
# Degree-zero Hom objects for finite simplicial sets

Source: Stacks Project, Tags 017I, 017J, 017K and 001Q
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Compatible maps indexed by all simplices. Source: Stacks, proof of Tag 017J
(auxiliary; not a blueprint node). -/
def SimplicialHomFamily {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t})
    (W : FormalCoproduct.{w} X.Etale) :=
  {f : ∀ n : ℕ, S.obj (op ⦋n⦌) → (W ⟶ K.obj (op ⦋n⦌)) //
    ∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
      f n s ≫ K.map φ.op = f m (S.map φ.op s)}

/-- Precomposition preserves the compatibility equations. Source: Stacks, proof of Tag 017J
(auxiliary; not a blueprint node).

Proof: for each operator `φ` and simplex `s`, associativity rewrites
`(g ≫ f n s) ≫ K.map φ.op` as `g ≫ (f n s ≫ K.map φ.op)`.
Use the compatibility equation of `f` to obtain `g ≫ f m (S.map φ.op s)`.
This is composition in the category of def-weil-pbc-semi-representable-object. -/
theorem SimplicialHomFamily.precomp_compatible {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {W W' : FormalCoproduct.{w} X.Etale} (f : SimplicialHomFamily K S W) (g : W' ⟶ W) :
    ∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
      (g ≫ f.val n s) ≫ K.map φ.op = g ≫ f.val m (S.map φ.op s) := by
  intro m n φ s
  rw [Category.assoc, f.property m n φ s]

/-- Precomposition of compatible families. Source: Stacks, Tag 017J
(auxiliary; not a blueprint node). -/
def SimplicialHomFamily.precomp {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {W W' : FormalCoproduct.{w} X.Etale} (f : SimplicialHomFamily K S W) (g : W' ⟶ W) :
    SimplicialHomFamily K S W' :=
  ⟨fun n s => g ≫ f.val n s, f.precomp_compatible g⟩

/-- The presheaf `W ↦ {S-families in K over W}` of compatible families, functorial by
precomposition. An object `Hom(S,K)_0` with universal family `u` is a pair `(H, u)` with
`(simplicialHomFamilyFunctor K S).IsRepresentedBy u` (def-weil-pbc-representing-object);
for `S` with finite nonempty degrees and finitely many nondegenerate simplices such a pair
exists by `exists_simplicial_hom_object` (lem-weil-pbc-simplicial-hom-object-exists).
Source: Stacks, Tags 017I, 017J and 001Q
(auxiliary; not a blueprint node). -/
def simplicialHomFamilyFunctor {X : Scheme.{u}}
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t}) :
    (FormalCoproduct.{w} X.Etale)ᵒᵖ ⥤ Type (max u w t) where
  obj W := SimplicialHomFamily K S W.unop
  map g := TypeCat.ofHom (fun f => SimplicialHomFamily.precomp f g.unop)
  map_id W := by
    rfl
  map_comp g h := by
    rfl

/-- Restriction of a family to a simplicial subset. Source: Stacks, Tag 017J
(auxiliary; not a blueprint node). -/
def SimplicialHomFamily.restrict {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    {W : FormalCoproduct.{w} X.Etale} (f : SimplicialHomFamily K S W)
    (A : S.Subcomplex) : SimplicialHomFamily K A.toSSet W :=
  ⟨fun n s => f.val n s.val, fun m n φ s => f.property m n φ s.val⟩

/-- The restriction morphism `Hom(S,K)_0 ⟶ Hom(A,K)_0` along a simplicial subset `A ⊆ S`:
for a family `u` over `H` (the universal family of a representing pair for `S`) and a pair
`(H', u')` representing the functor of `A`-families, the unique morphism `ρ : H ⟶ H'` with
`u'_s ∘ ρ = u_s` for all simplices `s` of `A`, i.e. the preimage of `u.restrict A` under the
bijection `g ↦ (u'_s ∘ g)_s` of `Functor.IsRepresentedBy`. Source: Stacks, Tags 017I and 017J
(auxiliary; not a blueprint node). -/
noncomputable def simplicialHomRestriction {X : Scheme.{u}}
    {K : SimplicialObject (FormalCoproduct.{w} X.Etale)} {S : SSet.{t}}
    (A : S.Subcomplex) {H H' : FormalCoproduct.{w} X.Etale}
    (u : SimplicialHomFamily K S H) {u' : SimplicialHomFamily K A.toSSet H'}
    (hu' : (simplicialHomFamilyFunctor K A.toSSet).IsRepresentedBy u') : H ⟶ H' :=
  (Equiv.ofBijective _ hu'.map_bijective).symm (u.restrict A)

end AlgebraicGeometry.Scheme
