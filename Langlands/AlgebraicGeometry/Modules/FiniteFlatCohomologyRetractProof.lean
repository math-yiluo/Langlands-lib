import Langlands.AlgebraicGeometry.Modules.FiniteFlatTrace
import Langlands.AlgebraicGeometry.Modules.BasicOpenHomGluing
import Langlands.AlgebraicGeometry.Modules.FiniteFlatCohomologyRetractAssembly
import Langlands.AlgebraicGeometry.Modules.FiniteFlatCohomologyRetractStatement

/-! # Cohomology retraction along a finite flat morphism of invertible rank -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

lemma nsmul_app_apply {M N : Y.Modules} (n : ℕ) (φ : M ⟶ N) (V : Y.Opens) (x : Γ(M, V)) :
    (n • φ).app V x = n • φ.app V x := by
  induction n with
  | zero => simp
  | succ n ih => simp [succ_nsmul, ih]

variable (f : X ⟶ Y) [IsFinite f] [Flat f] {d : ℕ} (hd : ∀ y, f.finrank y = d)
  (M : Y.Modules) [M.IsQuasicoherent]

/-- The trace `f_* f^* M ⟶ M` of a finite flat morphism of constant rank, glued from the local
traces over the free affine charts. -/
def trace : (AlgebraicGeometry.Scheme.Modules.pushforward f).obj
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ⟶ M :=
  BasisHomGluing.homOfBasicOpen (P := IsFreeChart f) (fun _ hV => hV.1)
    (fun _ g hV => IsFreeChart.basicOpen f hV g) (exists_isFreeChart f hd)
    (fun _ hV => localTrace f M hV.1) (fun _ hV g z => localTrace_basicOpen f M hV g z)

/-- The unit `M ⟶ f_* f^* M` followed by the trace is multiplication by the rank. -/
theorem unit_comp_trace :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      trace f hd M = d • 𝟙 M := by
  refine BasisHomGluing.hom_ext_of_basicOpen (P := IsFreeChart f) (fun _ hV => hV.1)
    (fun _ g hV => IsFreeChart.basicOpen f hV g) (exists_isFreeChart f hd) _ _ ?_
  intro V hV
  ext m
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, trace,
    BasisHomGluing.homOfBasicOpen_app _ _ _ _ _ V hV, nsmul_app_apply]
  exact localTrace_sectionPullback f M hd hV m

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules

/-- Over a field `K`, for a finite flat morphism `f : X ⟶ Y` of `K`-schemes of constant rank
`d` with `(d : K) ≠ 0` and a quasi-coherent `M` on `Y`, `Hⁿ(Y, M)` is a retract of
`Hⁿ(X, f^* M)`. -/
theorem finiteFlatCohomologyRetract : FiniteFlatCohomologyRetractStatement.{u} := by
  intro K _ X Y f hfin hflat _ d hd hrank M hM n
  exact finiteFlatCohomologyRetract_of_trace f M d hd
    (Langlands.Scheme.Modules.trace f.left hrank M)
    (Langlands.Scheme.Modules.unit_comp_trace f.left hrank M) n

end Langlands.AlgebraicGeometry.Modules
