import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentProof
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.SubgroupIntersection

/-! # Recovering a centralizer Borel from an ambient Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusCentralizerBorelConverse

private theorem range_comp_iso_transport {K : Scheme.{u}}
    {H G G' : GroupScheme K} (i : H ⟶ G) (e : G ≅ G') :
    SubgroupFunctor.range (i ≫ e.hom) =
      SubgroupFunctor.transport e (SubgroupFunctor.range i) := by
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X := by
    rw [← Grp.comp_hom_hom, e.hom_inv_id]
    rfl
  have he' : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G'.X := by
    rw [← Grp.comp_hom_hom, e.inv_hom_id]
    rfl
  ext U x
  change (∃ y : U ⟶ H.X, y ≫ (i ≫ e.hom).hom.hom = x) ↔
    ∃ y : U ⟶ H.X, y ≫ i.hom.hom = x ≫ e.inv.hom.hom
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp only [Grp.comp_hom_hom, Category.assoc, he, Category.comp_id]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change (y ≫ i.hom.hom) ≫ e.hom.hom.hom = x
    rw [hy, Category.assoc, he', Category.comp_id]

private theorem transport_inf {K : Scheme.{u}} {G G' : GroupScheme K}
    (e : G ≅ G') (F F' : SubgroupFunctor G) :
    SubgroupFunctor.transport e (F ⊓ F') =
      SubgroupFunctor.transport e F ⊓ SubgroupFunctor.transport e F' := rfl

end TorusCentralizerBorelConverse

variable {k : Type u} [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G)
    (hS : IsTorus S.toGrp) (hs : IsClosedSubgroup s)
    (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G)
    (hrep : (torusCentralizer s).IsRepresentedBy c) (hc : IsClosedSubgroup c)

include hS hs hrep hc

/-- Once every torus-containing ambient Borel has Borel intersection with the
centralizer, each Borel of the centralizer is such an intersection. -/
theorem exists_ambient_borel_of_torusCentralizer_intersections
    (hinter : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b → SubgroupFunctor.range s ≤ SubgroupFunctor.range b →
        IsBorelSubgroup (subgroupIntersectionFst c b))
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ C)
    (hd : IsBorelSubgroup d) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b ∧ SubgroupFunctor.range s ≤ SubgroupFunctor.range b ∧
        SubgroupFunctor.range (d ≫ c) =
          SubgroupFunctor.range c ⊓ SubgroupFunctor.range b := by
  have : Smooth S.X.hom := hS.smooth
  have : ConnectedSpace S.X.left := hS.connectedSpace
  have : Smooth C.X.hom := torusCentralizerSmooth k G S s hS hs C c hrep hc
  have : ConnectedSpace C.X.left := hS.connectedSpace_centralizer s hrep
  have : IsClosedImmersion c.hom.hom.left := hc
  have : IsAffineHom C.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  obtain ⟨B₀, b₀, f, hb₀, hf⟩ := solvableSubgroupBorelContainment k G S.toGrp s hs
    (isSolvableGroupScheme_of_isCommMonObj S.toGrp)
  have hs₀ : SubgroupFunctor.range s ≤ SubgroupFunctor.range b₀ := by
    rw [← hf]
    intro U x hx
    rw [SubgroupFunctor.mem_range] at hx ⊢
    rcases hx with ⟨y, rfl⟩
    exact ⟨y ≫ f.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  let I := subgroupIntersection c b₀
  let i : I ⟶ C := subgroupIntersectionFst c b₀
  have hi : IsBorelSubgroup i := hinter B₀ b₀ hb₀ hs₀
  obtain ⟨z, φ, hφ⟩ := (borelConjugacy k C).2 I D i d hi hd
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := z ≫ c.hom.hom
  let e : G ≅ G := G.innerIso g
  have hsfix : s ≫ e.hom = s := by
    apply (mem_torusCentralizer_base_iff s g).mp
    rw [← hrep.2]
    exact ⟨z, rfl⟩
  have hcfix : SubgroupFunctor.range (c ≫ e.hom) = SubgroupFunctor.range c := by
    rw [← innerIso_hom_comp c z]
    exact SubgroupFunctor.range_iso_comp (C.innerIso z) c
  have hifactor : (i ≫ c) ≫ e.hom = φ.hom ≫ (d ≫ c) := by
    rw [Category.assoc, ← innerIso_hom_comp c z, ← Category.assoc, hφ, Category.assoc]
  have hirange : SubgroupFunctor.range ((i ≫ c) ≫ e.hom) =
      SubgroupFunctor.range (d ≫ c) := by
    rw [hifactor, SubgroupFunctor.range_iso_comp]
  refine ⟨B₀, b₀ ≫ e.hom, hb₀.comp_iso e, ?_, ?_⟩
  · have h := SubgroupFunctor.range_comp_mono hs₀ e.hom
    rwa [hsfix] at h
  · rw [← hirange, TorusCentralizerBorelConverse.range_comp_iso_transport]
    have hrange : SubgroupFunctor.range (i ≫ c) =
        SubgroupFunctor.range c ⊓ SubgroupFunctor.range b₀ :=
      range_subgroupIntersectionHom c b₀
    rw [hrange, TorusCentralizerBorelConverse.transport_inf,
      ← TorusCentralizerBorelConverse.range_comp_iso_transport,
      ← TorusCentralizerBorelConverse.range_comp_iso_transport, hcfix]

end Langlands.GroupScheme
