import Langlands.GroupScheme.FiniteKernelFunctions
import Langlands.GroupScheme.AffineFiniteFunctionsRepresentation

/-! # A finite representation detecting a supplied homomorphism's kernel -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G Q H A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ Q}

/-- A homomorphism vanishing on the detector's finitely many functions kills
its full scheme-theoretic kernel equations. -/
theorem FiniteKernelDetector.comp_eq_zero (D : FiniteKernelDetector q) (r : H ⟶ G)
    (hr : ∀ a ∈ D.functions, (r ≫ q).hom.hom.left.appTop a = 0) : r ≫ q = 0 := by
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  let J := Ideal.span (D.functions : Set Γ(Q.X.left, ⊤))
  have hJ : J.map (r ≫ q).hom.hom.left.appTop.hom = ⊥ := by
    apply le_antisymm _ bot_le
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    intro a ha
    exact hr a ha
  have hpull : ((kernelι q).hom.hom.left.ker).comap r.hom.hom.left = ⊥ := by
    rw [D.ideal_eq, Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_map,
      ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    change Scheme.IdealSheafData.ofIdealTop
      (J.map (r ≫ q).hom.hom.left.appTop.hom) = ⊥
    rw [hJ]
    ext U
    simp [Scheme.IdealSheafData.ofIdealTop_ideal]
  have hker : (kernelι q).hom.hom.left.ker ≤ r.hom.hom.left.ker := by
    rw [← Scheme.IdealSheafData.map_bot r.hom.hom.left,
      Scheme.IdealSheafData.le_map_iff_comap_le, hpull]
  let l := IsClosedImmersion.lift (kernelι q).hom.hom.left r.hom.hom.left hker
  have hfac : l ≫ (kernelι q).hom.hom.left = r.hom.hom.left :=
    IsClosedImmersion.lift_fac _ _ hker
  have hbase : l ≫ (kernel q).X.hom = H.X.hom := by
    rw [← (kernelι q).hom.hom.w, ← Category.assoc, hfac, r.hom.hom.w]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change r.hom.hom.left ≫ q.hom.hom.left = H.X.hom ≫ η[Q.X].left
  calc
    r.hom.hom.left ≫ q.hom.hom.left =
        l ≫ (kernelι q).hom.hom.left ≫ q.hom.hom.left := by
      rw [← Category.assoc, hfac]
    _ = l ≫ (kernel q).X.hom ≫ η[Q.X].left := by
      rw [(kernel_isPullback_scheme q).w]
    _ = H.X.hom ≫ η[Q.X].left := by rw [← Category.assoc, hbase]

/-- If a finite representation captures the detector functions, it detects
triviality after any actual homomorphism into the source. -/
theorem FiniteKernelDetector.comp_eq_zero_of_contains (D : FiniteKernelDetector q)
    (ρ : Q ⟶ A)
    (hρ : ∀ a ∈ D.functions, a ∈ Set.range ρ.hom.hom.left.appTop.hom)
    (r : H ⟶ G) (hr : r ≫ q ≫ ρ = 0) : r ≫ q = 0 := by
  apply D.comp_eq_zero r
  intro a ha
  obtain ⟨b, hb⟩ := hρ a ha
  have hunit : η[Q.X].left ≫ ρ.hom.hom.left = η[A.X].left :=
    congrArg (fun f => f.left) (IsMonHom.one_hom ρ.hom.hom)
  have hbzero : η[A.X].left.appTop b = 0 := by
    rw [← hunit, Scheme.Hom.comp_appTop]
    change η[Q.X].left.appTop (ρ.hom.hom.left.appTop b) = 0
    rw [hb]
    exact D.vanishes a ha
  have he := congrArg (fun f : H ⟶ A => f.hom.hom.left.appTop b) hr
  change ((r ≫ q).hom.hom.left ≫ ρ.hom.hom.left).appTop b =
    (H.X.hom ≫ η[A.X].left).appTop b at he
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at he
  change (r ≫ q).hom.hom.left.appTop (ρ.hom.hom.left.appTop b) =
    H.X.hom.appTop (η[A.X].left.appTop b) at he
  simpa only [hb, hbzero, map_zero] using he

/-- One actual finite-dimensional representation retaining all kernel equations
of a supplied group homomorphism. -/
structure KernelDetectingRepresentation (q : G ⟶ Q) where
  dimension : ℕ
  hom : Q ⟶ GeneralLinear.groupScheme (Fin dimension) (CommRingCat.of k)
  detects : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (r : H ⟶ G),
    r ≫ q ≫ hom = 0 → r ≫ q = 0

/-- A Noetherian source admits a finite-dimensional target representation that
detects the same full kernel as its homomorphism to an affine target. -/
def kernelDetectingRepresentation [IsNoetherian G.X.left] [IsAffine Q.X.left]
    (q : G ⟶ Q) : KernelDetectingRepresentation q := by
  let D := finiteKernelDetector q
  let R := finiteFunctionsRepresentation Q D.functions
  exact
    { dimension := R.dimension
      hom := R.hom
      detects := fun _ r hr => D.comp_eq_zero_of_contains R.hom R.contains r hr }

end Langlands.GroupScheme
