import Langlands.AbelianScheme.BaseChangeCoherence
import Langlands.AbelianScheme.Tate.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Étale descent of rational homomorphisms of abelian schemes over a connected base -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

universe u

namespace Langlands.AbelianScheme

/-- For a commuting square `a ≫ g = a' ≫ g'` of scheme maps, the canonical
isomorphism between the two iterated pullbacks of an abelian scheme: undo the
first iterated pullback, transport along the equality of composites, and
redo the second one. -/
def baseChangeSquareIso {S W W' Z : Scheme.{u}} (g : W ⟶ S) (g' : W' ⟶ S)
    (a : Z ⟶ W) (a' : Z ⟶ W') (h : a ≫ g = a' ≫ g') (A : AbelianScheme S) :
    (baseChange a).obj ((baseChange g).obj A) ≅ (baseChange a').obj ((baseChange g').obj A) :=
  (baseChangeCompIso g a A).symm ≪≫ eqToIso (by rw [h]) ≪≫ baseChangeCompIso g' a' A

/-- Étale descent of rational homomorphisms over a connected base. Let `S` be a
connected locally noetherian scheme on which every positive integer is a unit,
and let `g k : W k ⟶ S` be étale morphisms from connected locally noetherian
schemes whose images cover `S`. Let `A` and `B` be abelian schemes over `S`,
and let `e k` be rational homomorphisms between their pullbacks to `W k`.
Suppose that, for every connected locally noetherian scheme `Z` with morphisms
`a : Z ⟶ W k` and `b : Z ⟶ W l` satisfying `a ≫ g k = b ≫ g l`, the pullbacks
of `e k` along `a` and of `e l` along `b` agree under the canonical
isomorphisms `baseChangeSquareIso`. Then some rational homomorphism from `A`
to `B` pulls back to `e k` along every `g k`. -/
def ConnectedEtaleRationalHomDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] [ConnectedSpace S],
    (∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤))) →
    ∀ (K : Type u) (W : K → Scheme.{u}) [∀ k, IsLocallyNoetherian (W k)]
      [∀ k, ConnectedSpace (W k)] (g : ∀ k, W k ⟶ S),
      (∀ k, Etale (g k)) → (∀ x : S, ∃ (k : K) (y : W k), g k y = x) →
    ∀ (A B : AbelianScheme S)
      (e : ∀ k, Hom0 ((baseChange (g k)).obj A) ((baseChange (g k)).obj B)),
      (∀ (k l : K) (Z : Scheme.{u}) [IsLocallyNoetherian Z] [ConnectedSpace Z]
          (a : Z ⟶ W k) (b : Z ⟶ W l) (h : a ≫ g k = b ≫ g l),
          comp0 _ _ _ (rationalBaseChangeHom a (e k))
              (homToHom0 (baseChangeSquareIso (g k) (g l) a b h B).hom) =
            comp0 _ _ _ (homToHom0 (baseChangeSquareIso (g k) (g l) a b h A).hom)
              (rationalBaseChangeHom b (e l))) →
      ∃ f : Hom0 A B, ∀ k, rationalBaseChangeHom (g k) f = e k

end Langlands.AbelianScheme
