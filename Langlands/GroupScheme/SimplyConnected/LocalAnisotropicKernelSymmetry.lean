import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelCartan

/-! # Symmetry of the actual anisotropic-kernel Cartan matrix -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData D} {ι : D ⟶ G}

/-- A type-A component gives equal Cartan entries in both directions from
its chosen vertex, including the case of a vertex outside the component. -/
theorem HasInnerTypeAComponent.cartan_symmetric {a : e.Vertex}
    (hA : e.HasInnerTypeAComponent a) (b : e.Vertex) :
    e.cartan a b = e.cartan b a := by
  classical
  by_cases hz : e.cartan a b = 0
  · exact hz.trans (e.pinning.rootDatum.pairing_eq_zero_iff'.mp hz).symm
  obtain ⟨n, _, q, hq, _⟩ := hA
  let a' := e.cartanComponentSelf a
  let b' : e.CartanComponent a := ⟨b, e.cartanConnected_of_cartan_ne_zero hz⟩
  have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M (q b') (q a'))
    (CartanMatrix.A_transpose n)
  exact (hq a' b').trans (hs.trans (hq b' a').symm)

/-- Transport symmetry of the actual kernel diagram to every pair of ambient
zero vertices. -/
theorem KernelComparison.zero_cartan_symmetric
    (h : d.KernelComparison ι e) (hA : ∀ a, e.HasInnerTypeAComponent a)
    (a b : d.zeroVertices) :
    d.cartan a.val b.val = d.cartan b.val a.val := by
  let q := h.vertexEquiv.symm
  have hq : ∀ x y : d.zeroVertices,
      d.cartan x.val y.val = e.cartan (q x) (q y) := by
    intro x y
    simpa only [q, Equiv.apply_symm_apply] using h.vertexEquiv_cartan (q x) (q y)
  exact (hq a b).trans (((hA (q a)).cartan_symmetric (q b)).trans (hq b a).symm)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The local component premise forces symmetry of the whole ambient zero
subdiagram, in the actual Cartan entries. -/
theorem zero_cartan_symmetric_of_local_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (a b : d.zeroVertices) :
    d.cartan a.val b.val = d.cartan b.val a.val := by
  let K := d.anisotropicKernelIndex
  exact K.comparison.zero_cartan_symmetric
    (hcomponents k K.kernel K.index K.anisotropic) a b

end Langlands.GroupScheme.TitsIndexData
