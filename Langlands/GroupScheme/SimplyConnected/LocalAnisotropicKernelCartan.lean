import Langlands.GroupScheme.Reductive.TitsKernelIndexChoice
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicCartanComponents

/-! # Type-A component consequences for the actual anisotropic-kernel diagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData D} {ι : D ⟶ G}

private theorem typeA_adjacent {n : ℕ} {i j : Fin n}
    (h : CartanMatrix.A n i j = -1) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [CartanMatrix.A, Matrix.of_apply] at h
  (split_ifs at h; omega)

/-- A type-A Cartan component cannot contain a vertex with three distinct
neighbors having Cartan entry `-1`. -/
theorem HasInnerTypeAComponent.not_three_neighbors {a : e.Vertex}
    (hA : e.HasInnerTypeAComponent a) (b c t : e.Vertex)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hb : e.cartan a b = -1) (hc : e.cartan a c = -1)
    (ht : e.cartan a t = -1) : False := by
  obtain ⟨n, -, q, hq, -⟩ := hA
  let a' : e.CartanComponent a := e.cartanComponentSelf a
  let b' : e.CartanComponent a :=
    ⟨b, e.cartanConnected_of_cartan_ne_zero (by rw [hb]; decide)⟩
  let c' : e.CartanComponent a :=
    ⟨c, e.cartanConnected_of_cartan_ne_zero (by rw [hc]; decide)⟩
  let t' : e.CartanComponent a :=
    ⟨t, e.cartanConnected_of_cartan_ne_zero (by rw [ht]; decide)⟩
  have hb' := typeA_adjacent ((hq a' b').symm.trans hb)
  have hc' := typeA_adjacent ((hq a' c').symm.trans hc)
  have ht' := typeA_adjacent ((hq a' t').symm.trans ht)
  have hbc' : (q b').val ≠ (q c').val :=
    fun h => hbc (congrArg Subtype.val (q.injective (Fin.ext h)))
  have hbt' : (q b').val ≠ (q t').val :=
    fun h => hbt (congrArg Subtype.val (q.injective (Fin.ext h)))
  have hct' : (q c').val ≠ (q t').val :=
    fun h => hct (congrArg Subtype.val (q.injective (Fin.ext h)))
  omega

/-- Transport the type-A valence obstruction through the actual kernel
comparison to the ambient zero subdiagram. -/
theorem KernelComparison.not_three_zero_neighbors
    (h : d.KernelComparison ι e) (hA : ∀ a, e.HasInnerTypeAComponent a)
    (a b c t : d.zeroVertices) (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hb : d.cartan a.val b.val = -1) (hc : d.cartan a.val c.val = -1)
    (ht : d.cartan a.val t.val = -1) : False := by
  let q := h.vertexEquiv.symm
  have hq : ∀ x y : d.zeroVertices,
      e.cartan (q x) (q y) = d.cartan x.val y.val := by
    intro x y
    simpa only [q, Equiv.apply_symm_apply] using
      (h.vertexEquiv_cartan (q x) (q y)).symm
  exact (hA (q a)).not_three_neighbors (q b) (q c) (q t)
    (q.injective.ne hbc) (q.injective.ne hbt) (q.injective.ne hct)
    ((hq a b).trans hb) ((hq a c).trans hc) ((hq a t).trans ht)

/-- If a full Galois element fixes one zero vertex, it fixes every adjacent
zero vertex whenever the kernel component has trivial internal full-star
action. -/
theorem KernelComparison.star_eq_of_fixed_zero_adjacent
    (h : d.KernelComparison ι e) (hA : ∀ a, e.HasInnerTypeAComponent a)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a b : d.zeroVertices)
    (hfix : d.star σ a.val = a.val) (hab : d.cartan a.val b.val ≠ 0) :
    d.star σ b.val = b.val := by
  let a' := h.vertexEquiv.symm a
  let b' := h.vertexEquiv.symm b
  have ha' : e.star σ a' = a' := by
    apply h.vertexEquiv.injective
    rw [h.vertexEquiv_star]
    change d.zeroStar σ (h.vertexEquiv (h.vertexEquiv.symm a)) =
      h.vertexEquiv (h.vertexEquiv.symm a)
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact hfix
  have hab' : e.cartan a' b' ≠ 0 := by
    have heq := h.vertexEquiv_cartan a' b'
    simp only [a', b', Equiv.apply_symm_apply] at heq
    rwa [← heq]
  obtain ⟨_, _, _, _, hstar⟩ := hA a'
  have hb' := hstar σ (by rw [ha']; exact e.cartanConnected_refl a')
    ⟨b', e.cartanConnected_of_cartan_ne_zero hab'⟩
  have heq := h.vertexEquiv_star σ b'
  rw [hb'] at heq
  have heq' := congrArg (fun x : d.zeroVertices => x.val) heq
  simpa only [b', Equiv.apply_symm_apply, zeroStar] using heq'.symm

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- Under the local component premise, no ambient zero subdiagram has a
vertex with three distinct `-1` neighbors. -/
theorem not_three_zero_neighbors_of_local_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G)
    (a b c t : d.zeroVertices) (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hb : d.cartan a.val b.val = -1) (hc : d.cartan a.val c.val = -1)
    (ht : d.cartan a.val t.val = -1) : False := by
  let K := d.anisotropicKernelIndex
  exact K.comparison.not_three_zero_neighbors
    (hcomponents k K.kernel K.index K.anisotropic) a b c t hbc hbt hct hb hc ht

/-- Under the local component premise, a fixed zero vertex forces fixation
of each adjacent zero vertex for the same full absolute Galois element. -/
theorem star_eq_of_fixed_zero_adjacent_of_local_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a b : d.zeroVertices)
    (hfix : d.star σ a.val = a.val) (hab : d.cartan a.val b.val ≠ 0) :
    d.star σ b.val = b.val := by
  let K := d.anisotropicKernelIndex
  exact K.comparison.star_eq_of_fixed_zero_adjacent
    (hcomponents k K.kernel K.index K.anisotropic) σ a b hfix hab

end Langlands.GroupScheme.TitsIndexData
