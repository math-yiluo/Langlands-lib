import Langlands.GroupScheme.AntiAffineBaseChange
import Mathlib.Topology.Connected.Clopen

/-! # Connectedness from the actual global-functions ring -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem preconnectedSpace_of_isDomain_globalSections
    (X : Scheme.{u}) [IsDomain Γ(X, ⊤)] : PreconnectedSpace X := by
  classical
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  by_cases h0 : s = ∅
  · exact Or.inl h0
  by_cases h1 : s = Set.univ
  · exact Or.inr h1
  exfalso
  let U : X.Opens := ⟨s, hs.isOpen⟩
  let V : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  have : Nonempty U := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h0
    exact ⟨⟨x, hx⟩⟩
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr h1
    exact ⟨⟨x, hx⟩⟩
  have huv : U ⊔ V = ⊤ := by
    ext x
    simp [U, V]
  have hdisj : U ⊓ V = ⊥ := by
    ext x
    simp [U, V]
  have : IsDomain Γ(X, U ⊔ V) := by rwa [huv]
  let e : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hdisj).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  have : IsDomain (Γ(X, U) × Γ(X, V)) :=
    e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  exact false_of_nontrivial_of_product_domain Γ(X, U) Γ(X, V)

/-- An anti-affine field group is connected, without finite-type or smoothness
hypotheses. -/
theorem IsAntiAffine.connectedSpace {k : Type u} [Field k]
    {N : GroupScheme (Spec (CommRingCat.of k))} (hN : IsAntiAffine N) :
    ConnectedSpace N.X.left := by
  have : IsIso N.X.hom.appTop := hN
  let e : Γ(N.X.left, ⊤) ≅ CommRingCat.of k :=
    (asIso N.X.hom.appTop).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of k)
  have : IsDomain Γ(N.X.left, ⊤) :=
    e.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have : PreconnectedSpace N.X.left := preconnectedSpace_of_isDomain_globalSections N.X.left
  have : Nonempty N.X.left :=
    ⟨η[N.X].left (IsLocalRing.closedPoint k)⟩
  constructor
  infer_instance

end Langlands.GroupScheme
