import Langlands.Representation.Archimedean.CompactSmoothAverage
import Langlands.Representation.Archimedean.SmoothFunctionalCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Derivatives of scalar evaluations on smooth unitary orbits -/

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Langlands.Archimedean.SmoothFunctionalOrbit

universe uA uG uE

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  [LieGroup 𝓘(ℝ, A) ∞ G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : G →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)

set_option backward.isDefEq.respectTransparency false in
omit [Group G] [LieGroup I ∞ G] in
private theorem inner_mfderiv {f : G → E} {g : G}
    (hf : MDifferentiableAt I 𝓘(ℝ, E) f g) (w : E) (X : A) :
    Inner.inner ℂ w (mfderiv I 𝓘(ℝ, E) f g X) =
      mfderiv I 𝓘(ℝ, ℂ) (fun h => Inner.inner ℂ w (f h)) g X := by
  let L := (innerSL ℂ w).restrictScalars ℝ
  change L (mfderiv I 𝓘(ℝ, E) f g X) = mfderiv I 𝓘(ℝ, ℂ) (L ∘ f) g X
  rw [mfderiv_comp g L.differentiableAt.mdifferentiableAt hf, ContinuousLinearMap.mfderiv_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [LieGroup I ∞ G] in
/-- The derivative of unitarity is skew symmetry on the genuine smooth vectors. -/
theorem inner_lieDerivative_eq_neg
    (hπ : ∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v)
    (u v : smoothVectors I π) (X : A) :
    Inner.inner ℂ (u : E) (lieDerivative I π X v) =
      -Inner.inner ℂ (lieDerivative I π X u) (v : E) := by
  let f := orbitMap π (u : E)
  let g := orbitMap π (v : E)
  have hf : MDifferentiableAt I 𝓘(ℝ, E) f 1 := u.property.mdifferentiableAt (by simp)
  have hg : MDifferentiableAt I 𝓘(ℝ, E) g 1 := v.property.mdifferentiableAt (by simp)
  have hpair : HasMFDerivAt I 𝓘(ℝ, E × E) (fun a => (f a, g a)) 1
      ((mfderiv I 𝓘(ℝ, E) f 1).prod (mfderiv I 𝓘(ℝ, E) g 1)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hf.hasMFDerivAt.prodMk hg.hasMFDerivAt
  have hi : HasMFDerivAt 𝓘(ℝ, E × E) 𝓘(ℝ, ℂ)
      (fun p : E × E => Inner.inner ℂ p.1 p.2) (f 1, g 1)
      (fderivInnerCLM ℂ (f 1, g 1)) :=
    ((isBoundedBilinearMap_inner (𝕜 := ℂ) (E := E)).hasFDerivAt (f 1, g 1)).hasMFDerivAt
  have he : (fun a => Inner.inner ℂ (f a) (g a)) = fun _ => Inner.inner ℂ (u : E) (v : E) :=
    funext fun a => hπ a u v
  have hd := (hi.comp 1 hpair).mfderiv
  change mfderiv I 𝓘(ℝ, ℂ) (fun a => Inner.inner ℂ (f a) (g a)) 1 = _ at hd
  rw [he, mfderiv_const] at hd
  have hs := congrArg (fun D : A →L[ℝ] ℂ => D X) hd.symm
  let df : E := mfderiv I 𝓘(ℝ, E) f 1 X
  let dg : E := mfderiv I 𝓘(ℝ, E) g 1 X
  change Inner.inner ℂ (f 1) dg + Inner.inner ℂ df (g 1) = 0 at hs
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [df, dg, f, g, orbitMap, map_one, one_apply_eq_self, lieDerivative] using hs

/-- A smooth test vector absorbs a genuine derivative word in the first
argument of the original inner product. -/
theorem exists_adjointWord
    (hπ : ∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v)
    (Xs : List A) (u : smoothVectors I π) :
    ∃ w : smoothVectors I π, ∀ v : smoothVectors I π,
      Inner.inner ℂ (u : E) (iteratedLieDerivative I π Xs v) = Inner.inner ℂ (w : E) (v : E) := by
  induction Xs generalizing u with
  | nil => exact ⟨u, fun _ => rfl⟩
  | cons X Xs ih =>
      obtain ⟨w, hw⟩ := ih (-(smoothLieDerivative I π X u))
      refine ⟨w, fun v => ?_⟩
      calc
        _ = -Inner.inner ℂ (lieDerivative I π X u)
            (smoothIteratedLieDerivative I π Xs v : E) := by
          rw [iteratedLieDerivative_cons, ← smoothIteratedLieDerivative_apply]
          exact inner_lieDerivative_eq_neg π hπ u (smoothIteratedLieDerivative I π Xs v) X
        _ = _ := by
          simpa only [Submodule.coe_neg, smoothLieDerivative_apply, smoothIteratedLieDerivative_apply,
            inner_neg_left] using hw v

/-- Every genuine word coordinate of a smooth orbit is a norm-smooth function. -/
theorem contMDiff_iteratedLieDerivative_orbit (Xs : List A) (v : smoothVectors I π) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun g => iteratedLieDerivative I π Xs (π g v)) := by
  have h := CompactSmoothAverage.contMDiff_orbit_iteratedLieDerivative
    (H := A) (N := G) π (v := fun g : G => π g (v : E))
    (CompactSmoothAverage.contMDiff_orbit_family π v.property) Xs
  simpa only [Function.comp_def, map_one, one_apply_eq_self, id_eq] using
    h.comp ((contMDiff_const : ContMDiff I I ∞ (fun _ : G => (1 : G))).prodMk contMDiff_id)

/-- The derivative of a word coordinate along right multiplication is
the same word applied to the translated genuine derived vector. -/
theorem mfderiv_iteratedLieDerivative_orbit
    (hπ : ∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v)
    (hdense : DenseRange ((↑) : smoothVectors I π → E))
    (Xs : List A) (v : smoothVectors I π) (g : G) (X : A) :
    mfderiv I 𝓘(ℝ, E) (fun h => iteratedLieDerivative I π Xs (π (g * h) v)) 1 X =
      iteratedLieDerivative I π Xs (π g (lieDerivative I π X v)) := by
  let F := fun h : G => iteratedLieDerivative I π Xs (π (g * h) v)
  let P := fun h : G => π (g * h) (v : E)
  have hF : MDifferentiableAt I 𝓘(ℝ, E) F 1 :=
    ((contMDiff_iteratedLieDerivative_orbit π Xs v).comp contMDiff_mul_left).mdifferentiableAt
      (by simp)
  have hP : MDifferentiableAt I 𝓘(ℝ, E) P 1 :=
    (v.property.comp contMDiff_mul_left).mdifferentiableAt (by simp)
  apply hdense.eq_of_inner_right ℂ
  intro u
  change Inner.inner ℂ (u : E) (mfderiv I 𝓘(ℝ, E) F 1 X) =
    Inner.inner ℂ (u : E) (iteratedLieDerivative I π Xs (π g (lieDerivative I π X v)))
  obtain ⟨w, hw⟩ := exists_adjointWord π hπ Xs u
  have he : (fun h => Inner.inner ℂ (u : E) (F h)) = fun h => Inner.inner ℂ (w : E) (P h) :=
    funext fun h => hw (smoothRepresentation I π (g * h) v)
  let d (f : G → ℂ) : ℂ := mfderiv I 𝓘(ℝ, ℂ) f 1 X
  calc
    Inner.inner ℂ (u : E) (mfderiv I 𝓘(ℝ, E) F 1 X) =
        d (fun h => Inner.inner ℂ (u : E) (F h)) :=
      inner_mfderiv hF u X
    _ = d (fun h => Inner.inner ℂ (w : E) (P h)) := congrArg d he
    _ = Inner.inner ℂ (w : E) (mfderiv I 𝓘(ℝ, E) P 1 X) := (inner_mfderiv hP w X).symm
    _ = Inner.inner ℂ (w : E) (π g (lieDerivative I π X v)) :=
      congrArg (Inner.inner ℂ (w : E)) (apply_lieDerivative I π g X v.property).symm
    _ = Inner.inner ℂ (u : E) (iteratedLieDerivative I π Xs (π g (lieDerivative I π X v))) :=
      (hw (smoothRepresentation I π g (smoothLieDerivative I π X v))).symm

variable [CompleteSpace E]

/-- Scalar evaluation by a derivative-continuous functional is genuinely
smooth on each orbit and has the right derivative prescribed by the action. -/
theorem contMDiff_mfderiv_smoothFunctional_orbit
    (hπ : ∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v)
    (hdense : DenseRange ((↑) : smoothVectors I π → E))
    (L : smoothVectors I π →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L)
    (v : smoothVectors I π) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g => L (smoothRepresentation I π g v)) ∧
      ∀ (g : G) (X : A),
        mfderiv I 𝓘(ℝ, ℂ) (fun h => L (smoothRepresentation I π (g * h) v)) 1 X =
          L (smoothRepresentation I π g (smoothLieDerivative I π X v)) := by
  classical
  obtain ⟨S, a, ha⟩ := exists_eq_sum_inner_iteratedLieDerivative I π L hL
  let c (i : S) (g : G) : ℂ := Inner.inner ℂ (a i) (iteratedLieDerivative I π i.val (π g v))
  have hc (i : S) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (c i) :=
    ((innerSL ℂ (a i)).restrictScalars ℝ).contMDiff.comp
      (contMDiff_iteratedLieDerivative_orbit π i.val v)
  have hsum (g : G) : L (smoothRepresentation I π g v) = ∑ i : S, c i g :=
    ha (smoothRepresentation I π g v)
  refine ⟨(contMDiff_finsetSum (t := Finset.univ) (fun i _ => hc i)).congr
    hsum, ?_⟩
  intro g X
  have hD (i : S) :
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun h => c i (g * h)) 1 :=
    ((hc i).comp contMDiff_mul_left).mdifferentiableAt (by simp)
  let D (i : S) : A →L[ℝ] ℂ := mfderiv I 𝓘(ℝ, ℂ) (fun h => c i (g * h)) 1
  have he : (fun h => L (smoothRepresentation I π (g * h) v)) =
      ∑ i : S, (fun h => c i (g * h)) := by
    funext h
    simpa only [Finset.sum_apply] using hsum (g * h)
  have hdiff : HasMFDerivAt I 𝓘(ℝ, ℂ) (∑ i : S, (fun h => c i (g * h))) 1 (∑ i : S, D i) :=
    HasMFDerivAt.sum (t := Finset.univ) (fun i _ => (hD i).hasMFDerivAt)
  rw [he, hdiff.mfderiv]
  change (∑ i : S, D i) X = _
  rw [sum_apply, ha (smoothRepresentation I π g (smoothLieDerivative I π X v))]
  apply Finset.sum_congr rfl
  intro i _
  have hi : MDifferentiableAt I 𝓘(ℝ, E)
      (fun h => iteratedLieDerivative I π i.val (π (g * h) v)) 1 :=
    ((contMDiff_iteratedLieDerivative_orbit π i.val v).comp contMDiff_mul_left).mdifferentiableAt
      (by simp)
  change mfderiv I 𝓘(ℝ, ℂ)
    (fun h => Inner.inner ℂ (a i) (iteratedLieDerivative I π i.val (π (g * h) v))) 1 X = _
  rw [← inner_mfderiv hi (a i) X, mfderiv_iteratedLieDerivative_orbit π hπ hdense]
  rfl

end Langlands.Archimedean.SmoothFunctionalOrbit

namespace Langlands.Archimedean

universe uA uG uE

/-- Derivative-continuous scalar evaluation on genuine unitary smooth orbits
is smooth and commutes with every real right orbit derivative. -/
def SmoothFunctionalOrbitStatement : Prop :=
  ∀ (A : Type uA) [NormedAddCommGroup A] [NormedSpace ℝ A]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace A G]
    [LieGroup 𝓘(ℝ, A) ∞ G] (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (π : G →* (E →L[ℂ] E)),
    (∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v) →
    DenseRange ((↑) : smoothVectors 𝓘(ℝ, A) π → E) →
    ∀ (L : smoothVectors 𝓘(ℝ, A) π →ₗ[ℂ] ℂ),
    IsContinuousOnSmoothVectors 𝓘(ℝ, A) π L →
    ∀ v : smoothVectors 𝓘(ℝ, A) π,
      ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞
        (fun g => L (smoothRepresentation 𝓘(ℝ, A) π g v)) ∧
      ∀ (g : G) (X : A),
        mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
          (fun h => L (smoothRepresentation 𝓘(ℝ, A) π (g * h) v)) 1 X =
        L (smoothRepresentation 𝓘(ℝ, A) π g (smoothLieDerivative 𝓘(ℝ, A) π X v))

theorem smoothFunctionalOrbit : SmoothFunctionalOrbitStatement.{uA,uG,uE} := by
  intro A _ _ G _ _ _ _ E _ _ _ π hπ hdense L hL v
  exact SmoothFunctionalOrbit.contMDiff_mfderiv_smoothFunctional_orbit π hπ hdense L hL v

end Langlands.Archimedean
