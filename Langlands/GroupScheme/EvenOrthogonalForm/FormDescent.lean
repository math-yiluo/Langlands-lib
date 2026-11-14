import Langlands.GroupScheme.EvenOrthogonalForm.SimilitudeCocycle
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties

/-! # Descent of a form of the split `SO_{2n}` to an identity component

Let `φ` be local isomorphisms from `H` to the split `SO_{2n}` over `K` along `Spec N ⟶ Spec K`
for a finite Galois extension `N / K`, whose Galois twists are conjugations by matrices `g_σ`.
Let `χ` be local isomorphisms from a smooth affine group `G'` to the split `O_{2n}` over `K`
along the same cover, whose values at `s` and `s ≫ σ*` differ by conjugation by `g_σ`. Then
`H` is isomorphic to the identity component of `G'`: the local isomorphisms
`χ⁰(s)⁻¹ ∘ φ(s)` are Galois invariant, hence independent of the cover point, and descend.
Smoothness transfers along local isomorphisms along `Spec N ⟶ Spec K`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.EvenOrthogonalForm

open OrthogonalMatrix

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}

/-- Smoothness of the structure morphism is preserved by isomorphisms of group schemes. -/
theorem smooth_of_groupIso {S : Scheme.{u}} {G H : GroupScheme S}
    (e : G ≅ H) (h : Smooth G.X.hom) : Smooth H.X.hom := by
  have sq : IsPullback e.inv.hom.hom.left H.X.hom G.X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso
      ⟨by rw [Category.comp_id]; exact e.inv.hom.hom.w⟩
  exact MorphismProperty.of_isPullback sq h

/-- A group scheme with local isomorphisms along `Spec N ⟶ Spec K` to a smooth group scheme
is smooth. -/
theorem smooth_of_localGroupIso {G G' : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G.X.hom] (χ : LocalGroupIso G' G (ringTest K N)) : Smooth G'.X.hom := by
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K N
  have : Surjective (ringTest K N).hom := hsurj
  have : Flat (ringTest K N).hom := hflat
  have : QuasiCompact (ringTest K N).hom := hqc
  apply smooth_of_baseChange (ringTest K N).hom G'
  have hG : Smooth ((GroupScheme.baseChange (ringTest K N).hom).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (ringTest K N).hom))
  exact smooth_of_groupIso χ.toBaseChangeIso.symm hG

variable [FiniteDimensional K N] [IsGalois K N]

/-- The comparison local isomorphisms `χ⁰(s)⁻¹ ∘ φ(s)` from `H` to the identity component
of `G'`. -/
def compareLocalIso {H G' : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom]
    (φ : LocalGroupIso H (splitGroup K n) (ringTest K N))
    (χ : LocalGroupIso G' (groupScheme (Fin n) (CommRingCat.of K)) (ringTest K N)) :
    LocalGroupIso H (identityComponent G') (ringTest K N) where
  toFun s := (φ.toFun s).trans
    ((LocalGroupIso.restrictIdentityComponent χ).toFun s).symm
  naturality t s h := by
    change ((LocalGroupIso.restrictIdentityComponent χ).toFun (t ≫ s)).symm
        (φ.toFun (t ≫ s) (t ≫ h)) =
      t ≫ ((LocalGroupIso.restrictIdentityComponent χ).toFun s).symm (φ.toFun s h)
    rw [φ.naturality]
    exact (LocalGroupIso.restrictIdentityComponent χ).symm.naturality t s _

/-- A form of the split `SO_{2n}` whose Galois twists are conjugations by `g_σ` is isomorphic
to the identity component of any smooth affine group with local isomorphisms to the split
`O_{2n}` that are Galois-equivariant for the same conjugations. -/
theorem nonempty_iso_identityComponent {H G' : GroupScheme (Spec (CommRingCat.of K))}
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom]
    (φ : LocalGroupIso H (splitGroup K n) (ringTest K N))
    (g : (N ≃ₐ[K] N) → GL (Fin n ⊕ Fin n) N)
    (hconj : ∀ (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
      (x : V ⟶ (splitGroup K n).X),
      splitMatrix ((galoisTwist φ σ).toFun s x) =
        (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s) *
          splitMatrix x *
            (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s))
    (χ : LocalGroupIso G' (groupScheme (Fin n) (CommRingCat.of K)) (ringTest K N))
    (hχ : ∀ (σ : N ≃ₐ[K] N) {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
      (u : V ⟶ G'.X),
      (pointsEquiv (Fin n) (CommRingCat.of K) V (χ.toFun (s ≫ ringTestMap K σ.toAlgHom) u) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤)) =
        (g σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s) *
          (pointsEquiv (Fin n) (CommRingCat.of K) V (χ.toFun s u) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Γ(V.left, ⊤)) *
            (↑(g σ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map (sectionScalars s)) :
    Nonempty (H ≅ identityComponent G') := by
  set χ0 := LocalGroupIso.restrictIdentityComponent χ with hχ0
  have hind : (compareLocalIso φ χ).IsIndependent := by
    apply LocalGroupIso.isIndependent_of_galois
    intro σ V s h
    change (χ0.toFun s).symm (φ.toFun s h) =
      (χ0.toFun (s ≫ ringTestMap K σ.toAlgHom)).symm
        (φ.toFun (s ≫ ringTestMap K σ.toAlgHom) h)
    have key : ∀ u : V ⟶ (identityComponent G').X,
        χ0.toFun (s ≫ ringTestMap K σ.toAlgHom) u =
          (galoisTwist φ σ).toFun s (χ0.toFun s u) := by
      intro u
      apply splitMatrix_injective
      rw [hconj]
      simp only [splitMatrix]
      rw [hχ0, LocalGroupIso.restrictIdentityComponent_toFun_comp,
        LocalGroupIso.restrictIdentityComponent_toFun_comp, hχ]
    have hφ : φ.toFun (s ≫ ringTestMap K σ.toAlgHom) h =
        (galoisTwist φ σ).toFun s (φ.toFun s h) := by
      rw [galoisTwist_toFun, MulEquiv.symm_apply_apply]
    rw [hφ, MulEquiv.eq_symm_apply, key, MulEquiv.apply_symm_apply]
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K N
  have : Surjective (ringTest K N).hom := hsurj
  have : Flat (ringTest K N).hom := hflat
  have : QuasiCompact (ringTest K N).hom := hqc
  exact ⟨(compareLocalIso φ χ).descend hind⟩

end Langlands.GroupScheme.EvenOrthogonalForm
