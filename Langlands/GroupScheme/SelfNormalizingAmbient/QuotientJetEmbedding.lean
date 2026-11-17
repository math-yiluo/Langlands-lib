import Langlands.GroupScheme.SelfNormalizingAmbient.OrbitMap
import Langlands.GroupScheme.HomogeneousQuotientMonomorphism
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # An explicit stabilized jet Grassmannian embedding of an actual quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SelfNormalizingAmbient

open Corepresented Module.Grassmannian.ProjectiveEmbedding

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (K : Ideal B) (n : ℕ) (hK : augIdeal e ^ (n + 1) ≤ K)
  {Q : Over (Spec R)} (q : (groupScheme F e).X ⟶ Q)

/-- Explicit classification data retained for the stabilized jet orbit of an actual
quotient, including the actual closed embedding and its factorization equation. -/
structure QuotientJetEmbeddingData where
  rank : ℕ
  complement : Submodule R (Fin rank → R)
  finite_complement : Module.Finite R complement
  projective_complement : Module.Projective R complement
  targetEquiv : ((B ⧸ K) × complement) ≃ₗ[R] (Fin rank → R)
  grassmannian : Rep R ((B ⧸ augIdeal e ^ (n + 1)) × complement) rank
  embedding : Q ⟶ Over.mk grassmannian.p
  fac : q ≫ embedding =
    orbitHom e hK targetEquiv grassmannian.pt B (e.homEquiv (𝟙 B))
  closed : IsClosedImmersion embedding.left

variable [Module.Finite R (B ⧸ augIdeal e ^ (n + 1))]
  [Module.Finite R (B ⧸ K)] [Module.Projective R (B ⧸ K)]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]

/-- A proper actual fpqc quotient with the stabilized jet stabilizer as its exact
all-test fibers admits an explicit closed embedding in the jet Grassmannian. -/
def quotientJetEmbeddingData
    (hq : ∀ (T : Over (Spec R)) (g h : T ⟶ (groupScheme F e).X),
      g ≫ q = h ≫ q ↔ Stabilizes e K (pointsEquiv F e T (g⁻¹ * h))) :
    QuotientJetEmbeddingData e K n hK q := Classical.choice (by
  obtain ⟨b, C, hCf, hCp, ⟨eW⟩⟩ := Module.exists_prod_linearEquiv_pi R (B ⧸ K)
  let : Module.Finite R C := hCf
  let : Module.Projective R C := hCp
  obtain ⟨Gr, p, pt, V, hpt, hV, hVaff, hVchart⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover
      R ((B ⧸ augIdeal e ^ (n + 1)) × C) b
  let D : Rep R ((B ⧸ augIdeal e ^ (n + 1)) × C) b :=
    ⟨Gr, p, pt, hpt, V, hV, hVaff, hVchart⟩
  let r : (groupScheme F e).X ⟶ Over.mk D.p :=
    orbitHom e hK eW D.pt B (e.homEquiv (𝟙 B))
  have hfib : ∀ (T : Over (Spec R)) (g h : T ⟶ (groupScheme F e).X),
      g ≫ q = h ≫ q ↔ g ≫ r = h ≫ r := fun T g h ↦
    (hq T g h).trans (comp_orbitHom_eq_iff hK eW D.hpt T g h).symm
  let f : Q ⟶ Over.mk D.p := HomogeneousQuotientComparison.desc q r
    (fun T g h hab ↦ (hfib T g h).mp hab)
  have hfac : q ≫ f = r := HomogeneousQuotientComparison.fac_desc q r _
  let : Mono f.left := HomogeneousQuotientComparison.mono_desc_of_fiber_iff q r hfib
  let : IsProper D.p := D.isProper_p
  have : IsProper (f.left ≫ D.p) := by
    rw [show f.left ≫ D.p = Q.hom from Over.w f]
    infer_instance
  let : IsProper f.left := IsProper.of_comp f.left D.p
  exact ⟨⟨b, C, hCf, hCp, eW, D, f, hfac,
    (IsClosedImmersion.iff_isProper_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩⟩⟩)

end Langlands.GroupScheme.SelfNormalizingAmbient
