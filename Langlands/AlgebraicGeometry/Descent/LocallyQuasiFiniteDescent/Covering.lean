import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Open charts through an fppf base change cover the descended presheaf

Let `p : G ⟶ h T` be a map of presheaves over `S`, and let `g i : V i ⟶ T` generate an fppf
covering sieve of `T` such that each base change of `p` along `g i` is represented by a scheme
`X' i`. If scheme charts `b k : h (Y k) ⟶ G` contain, around each point of each `X' i`, a Zariski
open neighbourhood on which the map to `G` factors through some chart, then the charts are jointly
locally surjective onto `G` in the fppf topology.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

open AlgebraicSpace

variable {S : Scheme.{u}}

private theorem map_uliftYonedaEquiv {G : Presheaf S} {U T : Over S}
    (a : (schemeYoneda S).obj U ⟶ G) (f : T ⟶ U) :
    G.map f.op (uliftYonedaEquiv a) = a.app (op T) (ULift.up f) :=
  congrArg (fun n : (schemeYoneda S).obj U ⟶ G => n.app (op T) (ULift.up f))
    (uliftYonedaEquiv.symm_apply_apply a)

/-- If every point of `X` has a Zariski open neighbourhood on which `a` factors through one of the
charts `b k`, then the charts cover the universal section of `a` in the fppf topology. -/
theorem imageSieve_mem_of_charts {G : Presheaf S} {X : Over S}
    (a : (schemeYoneda S).obj X ⟶ G)
    {K : Type u} {Y : K → Over S} (b : ∀ k, (schemeYoneda S).obj (Y k) ⟶ G)
    (hcov : ∀ ξ : X.left, ∃ (k : K) (U : X.left.Opens)
      (z : Over.mk (U.ι ≫ X.hom) ⟶ Y k), ξ ∈ U ∧
        (schemeYoneda S).map z ≫ b k =
          (schemeYoneda S).map (Over.homMk U.ι : Over.mk (U.ι ≫ X.hom) ⟶ X) ≫ a) :
    CategoryTheory.Presheaf.imageSieve (Sigma.desc b) (uliftYonedaEquiv a) ∈
      fppfTopology S X := by
  choose k U z hξ hz using hcov
  have hq : Sieve.ofArrows (fun ξ => Over.mk ((U ξ).ι ≫ X.hom))
      (fun ξ => (Over.homMk (U ξ).ι : Over.mk ((U ξ).ι ≫ X.hom) ⟶ X)) ∈
        fppfTopology S X := by
    let 𝒰 := Scheme.Cover.mkOfCovers
      (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      X.left (fun ξ => (U ξ).toScheme) (fun ξ => (U ξ).ι)
      (fun ξ => ⟨ξ, ⟨ξ, hξ ξ⟩, rfl⟩) (fun _ => inferInstance)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology
  apply (fppfTopology S).superset_covering ?_ hq
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro ξ
  refine ⟨(Sigma.ι (fun k => (schemeYoneda S).obj (Y k)) (k ξ)).app _ (ULift.up (z ξ)), ?_⟩
  have hs := congrArg (fun n => n.app (op (Over.mk ((U ξ).ι ≫ X.hom))) (ULift.up (z ξ)))
    (Sigma.ι_comp_desc b (k ξ))
  have h1 := congrArg uliftYonedaEquiv (hz ξ)
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map,
    uliftYonedaEquiv_uliftYoneda_map] at h1
  exact hs.trans (h1.trans (map_uliftYonedaEquiv a _).symm)

/-- Open charts through the represented base changes of `p` along an fppf covering family are
jointly fppf locally surjective onto `G`. -/
theorem isLocallySurjective_sigmaDesc_of_charts {G : Presheaf S} {T : Over S}
    (p : G ⟶ (schemeYoneda S).obj T) {I : Type u} {V : I → Over S} (g : ∀ i, V i ⟶ T)
    (hg : Sieve.ofArrows V g ∈ fppfTopology S T) {X' : I → Over S} (x' : ∀ i, X' i ⟶ V i)
    (a' : ∀ i, (schemeYoneda S).obj (X' i) ⟶ G)
    (hpb : ∀ i, IsPullback (a' i) ((schemeYoneda S).map (x' i)) p
      ((schemeYoneda S).map (g i)))
    {K : Type u} {Y : K → Over S} (b : ∀ k, (schemeYoneda S).obj (Y k) ⟶ G)
    (hcov : ∀ i (ξ : (X' i).left), ∃ (k : K) (U : (X' i).left.Opens)
      (z : Over.mk (U.ι ≫ (X' i).hom) ⟶ Y k), ξ ∈ U ∧
        (schemeYoneda S).map z ≫ b k =
          (schemeYoneda S).map (Over.homMk U.ι : Over.mk (U.ι ≫ (X' i).hom) ⟶ X' i) ≫ a' i) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc b) := by
  constructor
  intro Z y
  apply (fppfTopology S).transitive
    ((fppfTopology S).pullback_stable (p.app (op Z) y).down hg)
  intro Z' f hf
  obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff V g _).1 hf
  have hp : p.app (op Z') (G.map f.op y) =
      ((schemeYoneda S).map (g i)).app (op Z') (ULift.up c) := by
    rw [NatTrans.naturality_apply]
    change ULift.up (f ≫ (p.app (op Z) y).down) = ULift.up (c ≫ g i)
    rw [hc]
  obtain ⟨⟨w⟩, hw, -⟩ := Types.exists_of_isPullback ((hpb i).app (op Z')) _ _ hp
  rw [CategoryTheory.Presheaf.pullback_imageSieve, ← hw, ← map_uliftYonedaEquiv,
    ← CategoryTheory.Presheaf.pullback_imageSieve]
  exact (fppfTopology S).pullback_stable w (imageSieve_mem_of_charts (a' i) b (hcov i))

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
