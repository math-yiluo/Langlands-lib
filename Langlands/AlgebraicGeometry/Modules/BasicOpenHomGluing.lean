import Langlands.AlgebraicGeometry.Modules.BasisHomGluing

/-! # Gluing morphisms of module sheaves from compatible maps on basic opens -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Langlands.Scheme.Modules.BasisHomGluing

open OpenCoverHomGluing

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- Sections of a module agreeing on some open neighbourhood of every point of `O` agree. -/
lemma eq_of_forall_mem {N : Y.Modules} {O : Y.Opens} (s t : Γ(N, O))
    (h : ∀ y ∈ O, ∃ (W : Y.Opens) (hWO : W ≤ O), y ∈ W ∧
      N.presheaf.map (homOfLE hWO).op s = N.presheaf.map (homOfLE hWO).op t) : s = t := by
  let ι := {W : Y.Opens // ∃ hWO : W ≤ O,
    N.presheaf.map (homOfLE hWO).op s = N.presheaf.map (homOfLE hWO).op t}
  refine TopCat.Sheaf.eq_of_locally_eq' (sheafAb N) (fun W : ι => W.1) O
    (fun W => homOfLE W.2.1) ?_ s t (fun W => W.2.2)
  intro y hy
  obtain ⟨W, hWO, hyW, hW⟩ := h y hy
  exact Opens.mem_iSup.mpr ⟨⟨W, hWO, hW⟩, hyW⟩

variable {P : Y.Opens → Prop}
  (hPaff : ∀ V, P V → IsAffineOpen V)
  (hPbasic : ∀ V (g : Γ(Y, V)), P V → P (Y.basicOpen g))
  (hPcover : ∀ y : Y, ∃ V, P V ∧ y ∈ V)

include hPaff hPbasic hPcover in
/-- Affine opens closed under basic opens and covering `Y` form a basis. -/
lemma isBasis_of_basicOpen (y : Y) (U : Y.Opens) (hy : y ∈ U) : ∃ V, P V ∧ y ∈ V ∧ V ≤ U := by
  obtain ⟨V, hV, hyV⟩ := hPcover y
  obtain ⟨g, hgU, hyg⟩ := (hPaff V hV).exists_basicOpen_le (V := U) ⟨y, hy⟩ hyV
  exact ⟨Y.basicOpen g, hPbasic V g hV, hyg, hgU⟩

include hPaff hPbasic hPcover in
/-- Morphisms of modules agreeing on every `P`-open agree. -/
lemma hom_ext_of_basicOpen {N M : Y.Modules} (f g : N ⟶ M)
    (h : ∀ V : Y.Opens, P V → f.app V = g.app V) : f = g :=
  hom_ext_of_basis (isBasis_of_basicOpen hPaff hPbasic hPcover) f g h

variable {N M : Y.Modules} (θ : ∀ V, P V → (Γ(N, V) →ₗ[Γ(Y, V)] Γ(M, V)))
  (hθ : ∀ V (hV : P V) (g : Γ(Y, V)) (n : Γ(N, V)),
    θ (Y.basicOpen g) (hPbasic V g hV) (N.presheaf.map (homOfLE (Y.basicOpen_le g)).op n) =
      M.presheaf.map (homOfLE (Y.basicOpen_le g)).op (θ V hV n))

include hPaff hθ in
/-- Compatibility along basic opens implies compatibility along all inclusions of `P`-opens. -/
lemma compat_of_basicOpen (V V' : Y.Opens) (hV : P V) (hV' : P V') (h : V' ≤ V)
    (s : Γ(N, V)) :
    M.presheaf.map (homOfLE h).op (θ V hV s) = θ V' hV' (N.presheaf.map (homOfLE h).op s) := by
  have key : ∀ {V : Y.Opens} (hV : P V) (g : Γ(Y, V)) (W : Y.Opens) (hW : P W) (hWV : W ≤ V)
      (s : Γ(N, V)), W = Y.basicOpen g →
      θ W hW (N.presheaf.map (homOfLE hWV).op s) = M.presheaf.map (homOfLE hWV).op (θ V hV s) := by
    rintro V hV g W hW hWV s rfl
    exact hθ V hV g s
  apply eq_of_forall_mem
  intro y hy
  obtain ⟨f, g, hfg, hyf⟩ :=
    exists_basicOpen_le_affine_inter (hPaff V' hV') (hPaff V hV) y ⟨hy, h hy⟩
  refine ⟨Y.basicOpen f, Y.basicOpen_le f, hyf, ?_⟩
  have hW : P (Y.basicOpen f) := hPbasic V' f hV'
  rw [map_map_eq _ _ ((Y.basicOpen_le f).trans h),
    ← key hV' f _ hW (Y.basicOpen_le f) _ rfl,
    map_map_eq _ _ ((Y.basicOpen_le f).trans h),
    key hV g _ hW _ s hfg]

/-- The morphism of modules glued from linear maps on the `P`-opens that are compatible along
basic opens. -/
def homOfBasicOpen : N ⟶ M :=
  hom (isBasis_of_basicOpen hPaff hPbasic hPcover) θ (compat_of_basicOpen hPaff hPbasic θ hθ)

/-- On a `P`-open `V`, the glued morphism is `θ V`. -/
lemma homOfBasicOpen_app (V : Y.Opens) (hV : P V) (n : Γ(N, V)) :
    (homOfBasicOpen hPaff hPbasic hPcover θ hθ).app V n = θ V hV n :=
  hom_app_basis _ θ _ V hV n

include hPaff hPbasic hPcover hθ in
/-- Linear maps on the `P`-opens, compatible with restriction to basic opens, come from a
morphism of modules. -/
theorem exists_hom_of_basicOpen :
    ∃ φ : N ⟶ M, ∀ (V : Y.Opens) (hV : P V) (n : Γ(N, V)), φ.app V n = θ V hV n :=
  ⟨homOfBasicOpen hPaff hPbasic hPcover θ hθ, homOfBasicOpen_app hPaff hPbasic hPcover θ hθ⟩

end Langlands.Scheme.Modules.BasisHomGluing
