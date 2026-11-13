import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # Central endomorphisms of an induced representation through Frobenius reciprocity -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Let `σ` be a smooth representation of `M(F)` and `I = i_P^G`, `J = r_P^G`. Suppose every
`M(F)`-map `h : J(I σ) → σ` that intertwines `J(I a)` with `a` for every `a ∈ End(σ)` vanishes on
the classes of the induced functions that vanish at the identity. Then the centre of
`End(I σ)` is the set of `I(z)`, `z` central in `End(σ)`, that commute with `End(I σ)`. -/
theorem inducedCenter_eq_of_kernelVanishing :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (P M N : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)),
        haveI := hl.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
        haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
        haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
        ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M),
        let I := leviInductionFunctor p l r hp hr hl hmul
        let J := leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul
        (∀ h : (J.obj (I.obj σ)).representation.IntertwiningMap σ.representation,
          (∀ (a : σ ⟶ σ) (y : J.obj (I.obj σ)),
            h (SmoothRep.hom (J.map (I.map a)) y) = SmoothRep.hom a (h y)) →
          ∀ f : I.obj σ,
            Induction.eval (pointImage p)
              (inducingRepresentation
                (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
                (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
                (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f 1 = 0 →
            h (Jacquet.Localization.mk (I.obj σ).representation (pointImage (r ≫ p)) 1 f) = 0) →
        (Subring.center (End (I.obj σ)) : Set (End (I.obj σ))) =
          {x : End (I.obj σ) | ∃ z ∈ Subring.center (End σ),
            x = I.map z ∧ ∀ a : End (I.obj σ), a * x = x * a} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ I J hvan
  obtain ⟨e, he⟩ := leviFrobeniusReciprocity k G hG P M N p l r hp hl hr hmul (I.obj σ) σ
  let hsd := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hcl := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let ev : I.obj σ → σ := fun f => Induction.eval (pointImage p)
    (inducingRepresentation hsd hcl (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f 1
  let mk := Jacquet.Localization.mk (I.obj σ).representation (pointImage (r ≫ p)) 1
  have hmk : Function.Surjective mk := Jacquet.Localization.mk_surjective _ _ _
  -- Evaluation at the identity is natural in `σ`.
  have hev (a : σ ⟶ σ) (f : I.obj σ) : ev (SmoothRep.hom (I.map a) f) = SmoothRep.hom a (ev f) :=
    rfl
  -- The Jacquet functor acts on classes through the induced map.
  have hJ (g : I.obj σ ⟶ I.obj σ) (f : I.obj σ) :
      SmoothRep.hom (J.map g) (mk f) = mk (SmoothRep.hom g f) := rfl
  -- The Frobenius image of an endomorphism `y` commuting with `I(End σ)` intertwines.
  have hcomm (y : I.obj σ ⟶ I.obj σ) (hy : ∀ a : σ ⟶ σ, I.map a ≫ y = y ≫ I.map a)
      (a : σ ⟶ σ) (w : J.obj (I.obj σ)) :
      e (SmoothRep.hom y) (SmoothRep.hom (J.map (I.map a)) w) =
        SmoothRep.hom a (e (SmoothRep.hom y) w) := by
    obtain ⟨f, rfl⟩ := hmk w
    rw [hJ, he, he]
    have := congrArg (fun g => SmoothRep.hom g f) (hy a)
    change SmoothRep.hom y (SmoothRep.hom (I.map a) f) =
      SmoothRep.hom (I.map a) (SmoothRep.hom y f) at this
    rw [this]
    exact hev a _
  ext x
  constructor
  · intro hx
    have hxc : ∀ a : End (I.obj σ), a * x = x * a := Subring.mem_center_iff.mp hx
    let h := e (SmoothRep.hom x)
    let ε := e (SmoothRep.hom (𝟙 (I.obj σ)))
    have hh : ∀ (a : σ ⟶ σ) (w : J.obj (I.obj σ)),
        h (SmoothRep.hom (J.map (I.map a)) w) = SmoothRep.hom a (h w) :=
      hcomm x (fun a => (hxc (I.map a)).symm)
    have hε : ∀ (a : σ ⟶ σ) (w : J.obj (I.obj σ)),
        ε (SmoothRep.hom (J.map (I.map a)) w) = SmoothRep.hom a (ε w) :=
      hcomm (𝟙 _) (fun a => by rw [Category.comp_id, Category.id_comp])
    have hεmk (f : I.obj σ) : ε (mk f) = ev f := he _ f
    have hhmk (f : I.obj σ) : h (mk f) = ev (SmoothRep.hom x f) := he _ f
    have hker : LinearMap.ker ε.toLinearMap ≤ LinearMap.ker h.toLinearMap := by
      intro w hw
      obtain ⟨f, rfl⟩ := hmk w
      have hw' : ev f = 0 := by
        rw [← hεmk]
        exact hw
      exact hvan h hh f hw'
    have hsurj : Function.Surjective ε := by
      intro v
      obtain ⟨f, hf⟩ := normalizedInduction_eval_surjective hsd hcl
        (continuous_projection_pointImage p l r hp hl hr hmul)
        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ) v
      exact ⟨mk f, (hεmk f).trans hf⟩
    -- `c` is the unique linear map with `c (ε w) = h w`.
    let c0 : σ →ₗ[ℂ] σ := (LinearMap.ker ε.toLinearMap).liftQ h.toLinearMap hker ∘ₗ
      (ε.toLinearMap.quotKerEquivOfSurjective hsurj).symm.toLinearMap
    have hc0 (w : J.obj (I.obj σ)) : c0 (ε w) = h w := by
      change (LinearMap.ker ε.toLinearMap).liftQ h.toLinearMap hker
        ((ε.toLinearMap.quotKerEquivOfSurjective hsurj).symm (ε.toLinearMap w)) = h w
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
      rfl
    have hc0eq (m : rationalPoints M) (v : σ) :
        c0 (σ.representation m v) = σ.representation m (c0 v) := by
      obtain ⟨w, rfl⟩ := hsurj v
      rw [← Representation.IntertwiningMap.isIntertwining _ _ ε m w, hc0, hc0,
        Representation.IntertwiningMap.isIntertwining _ _ h m w]
    let cS : End σ := SmoothRep.ofHom ⟨c0, fun m => LinearMap.ext (hc0eq m)⟩
    have hcS (w : J.obj (I.obj σ)) : SmoothRep.hom cS (ε w) = h w := hc0 w
    have hextM {f g : σ ⟶ σ} (hfg : ∀ v, SmoothRep.hom f v = SmoothRep.hom g v) : f = g :=
      congrArg SmoothRep.ofHom (Representation.IntertwiningMap.ext (LinearMap.ext hfg))
    -- `c` is central in `End σ`.
    have hcen : cS ∈ Subring.center (End σ) := by
      refine Subring.mem_center_iff.mpr fun a => hextM fun v => ?_
      obtain ⟨w, rfl⟩ := hsurj v
      change SmoothRep.hom a (SmoothRep.hom cS (ε w)) =
        SmoothRep.hom cS (SmoothRep.hom a (ε w))
      rw [← hε a w, hcS, hcS, hh]
    -- `x` and `I(c)` have the same Frobenius image, so they are equal.
    have hx : SmoothRep.hom x = SmoothRep.hom (I.map cS) := by
      apply e.injective
      refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
      obtain ⟨f, rfl⟩ := hmk w
      change h (mk f) = e (SmoothRep.hom (I.map cS)) (mk f)
      calc h (mk f) = SmoothRep.hom cS (ε (mk f)) := (hcS _).symm
        _ = SmoothRep.hom cS (ev f) := by rw [hεmk]
        _ = ev (SmoothRep.hom (I.map cS) f) := (hev cS f).symm
        _ = e (SmoothRep.hom (I.map cS)) (mk f) := (he _ f).symm
    exact ⟨cS, hcen, congrArg SmoothRep.ofHom hx, hxc⟩
  · rintro ⟨z, _, _, hz⟩
    exact Subring.mem_center_iff.mpr hz

end Langlands.Aubert.General.RepresentedParabolic
