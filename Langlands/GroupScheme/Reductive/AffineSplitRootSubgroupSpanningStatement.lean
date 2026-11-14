import Langlands.GroupScheme.Reductive.LocalSplitCell

/-! # Statement: subgroups directly spanned by root groups over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Subgroups directly spanned by root groups over an affine base** (Conrad, *Reductive
group schemes* (2014), Theorem 5.1.13, Proposition 5.1.14 and Proposition 5.1.16(1)). Let `G`
be a reductive group over `Spec R`, split by a closed coordinate torus `i : 𝔾ₘ^I ⟶ G` with
fibrewise root datum `P`, and let `u α : 𝔾ₐ ⟶ G` parametrize the root group of each root `α`.

1. For every base `b` and all enumerations of the negative and the positive roots, the
   big-cell map `𝔾ₐᵐ × T × 𝔾ₐⁿ ⟶ G`, `(v, t, w) ↦ (∏ₖ u_{neg k}(vₖ)) i(t) (∏ₖ u_{pos k}(wₖ))`,
   is an open immersion.
2. For every base `b` and every enumeration of the positive roots, the map
   `T × 𝔾ₐⁿ ⟶ G`, `(t, w) ↦ i(t) ∏ₖ u_{pos k}(wₖ)`, is an isomorphism onto a closed
   subgroup of `G` (the semidirect product `T ⋉ U_{Φ⁺}`).
3. For every closed set `Ψ` of roots with `Ψ ∩ -Ψ = ∅` there is a smooth closed subgroup
   `U_Ψ`, normalized by the torus, with connected unipotent geometric fibres, such that for
   every enumeration of `Ψ` the multiplication map `𝔾ₐⁿ ⟶ G`, `w ↦ ∏ₖ u_{e k}(wₖ)`, is an
   isomorphism onto `U_Ψ`.
4. For roots `a`, `c` with `c ≠ ±a` and every enumeration of the roots `pa + qc` with
   `p, q > 0`, there are such exponents and global functions `C` on `Spec R` with
   `u_a(x) u_c(y) u_a(-x) u_c(-y) = ∏ₖ u_{pa+qc}(C_k xᵖ yᑫ)` on every test scheme. -/
def AffineSplitRootSubgroupSpanningStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ u : J → (Ga R ⟶ G), (∀ α, IsRootParametrization i (P.root α) (u α)) →
      (∀ (b : P.Base) (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α})
          (pos : Fin n ≃ {α // b.IsPos α}),
        IsOpenImmersion (cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))).left) ∧
      (∀ (b : P.Base) (n : ℕ) (pos : Fin n ≃ {α // b.IsPos α}),
        ∃ (B : GroupScheme (Spec (CommRingCat.of R))) (jB : B ⟶ G)
          (φ : cellObj R I 0 n ≅ B.X),
          IsClosedSubgroup jB ∧
            φ.hom ≫ jB.hom.hom = cellMap i u (Fin.elim0 : Fin 0 → J) (fun k => (pos k : J))) ∧
      (∀ Ψ : Set J,
        (∀ a ∈ Ψ, ∀ c ∈ Ψ, ∀ d : J, P.root d = P.root a + P.root c → d ∈ Ψ) →
        (∀ a ∈ Ψ, ∀ c ∈ Ψ, P.root a + P.root c ≠ 0) →
        ∃ (H : GroupScheme (Spec (CommRingCat.of R))) (j : H ⟶ G),
          IsClosedSubgroup j ∧ Smooth H.X.hom ∧
          (∀ (Z : Over (Spec (CommRingCat.of R)))
            (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (h : Z ⟶ H.X),
            ∃ h' : Z ⟶ H.X,
              (t ≫ i.hom.hom) * (h ≫ j.hom.hom) * (t ≫ i.hom.hom)⁻¹ = h' ≫ j.hom.hom) ∧
          (∀ s : Spec (CommRingCat.of R),
            ConnectedSpace (geometricFiber H s).X.left ∧ IsUnipotent (geometricFiber H s)) ∧
          ∀ (n : ℕ) (e : Fin n ≃ Ψ),
            ∃ φ : (VectorGroup.groupScheme (CommRingCat.of R) n).X ≅ H.X,
              φ.hom ≫ j.hom.hom =
                orderedProduct u (fun k => ((e k : Ψ) : J)) _
                  (VectorGroup.coordinates (CommRingCat.of R) n _ (𝟙 _)).toAdd) ∧
      ∀ a c : J, P.root c ≠ P.root a → P.root c ≠ -P.root a →
        ∀ (n : ℕ) (e : Fin n ≃
            {d : J // ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root d = p • P.root a + q • P.root c}),
          ∃ (p q : Fin n → ℕ) (C : Fin n → R),
            (∀ k, 0 < p k ∧ 0 < q k ∧
              P.root (e k : J) = p k • P.root a + q k • P.root c) ∧
            ∀ (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)),
              rootPoint (u a) Z x * rootPoint (u c) Z y * rootPoint (u a) Z (-x) *
                  rootPoint (u c) Z (-y) =
                orderedProduct u (fun k => (e k : J)) Z
                  (fun k => scalarMap Z (C k) * x ^ p k * y ^ q k)

end Langlands.GroupScheme
