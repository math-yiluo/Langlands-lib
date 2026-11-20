import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyClosedEmbeddingStatement
import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyUniversallyClosedStatement
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamilyNormalizer
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Reducing the closed embedding of `G / N_G(T)` into the subtori of `GL_m` to universal closedness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SelfCentralizingConjugacyClosedEmbeddingReduction

section FppfDescent

variable {S : Scheme.{u}}

/-- A morphism of relative schemes whose underlying morphism is flat, surjective and
locally of finite presentation is an epimorphism. -/
theorem epi_of_fppf {V U : Over S} (c : V ⟶ U) [Flat c.left] [Surjective c.left]
    [LocallyOfFinitePresentation c.left] : Epi c :=
  Over.epi_of_epi_left c

/-- Factorization through a monomorphism descends along an fppf morphism. -/
theorem exists_factor_of_fppf {U V X Z : Over S} (c : V ⟶ U) [Flat c.left]
    [Surjective c.left] [LocallyOfFinitePresentation c.left] (m : Z ⟶ X) [Mono m]
    (y : U ⟶ X) (z : V ⟶ Z) (hz : z ≫ m = c ≫ y) : ∃ w : U ⟶ Z, w ≫ m = y := by
  have h : ∀ (T : Over S) (a b : T ⟶ V), a ≫ c = b ≫ c → a ≫ z = b ≫ z := by
    intro T a b hab
    apply (cancel_mono m).mp
    rw [Category.assoc, Category.assoc, hz, ← Category.assoc, hab, Category.assoc]
  refine ⟨HomogeneousQuotientComparison.desc c z h, ?_⟩
  have : Epi c := epi_of_fppf c
  apply (cancel_epi c).mp
  rw [HomogeneousQuotientComparison.fac_desc_assoc, hz]

/-- The pullback of an fppf morphism `q : A ⟶ B` along a point `d : U ⟶ B`. -/
theorem exists_fppf_lift {A B U : Over S} (q : A ⟶ B) [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] (d : U ⟶ B) :
    ∃ (V : Over S) (c : V ⟶ U) (a : V ⟶ A), Flat c.left ∧ Surjective c.left ∧
      LocallyOfFinitePresentation c.left ∧ c ≫ d = a ≫ q := by
  let V : Over S := Over.mk (pullback.fst d.left q.left ≫ U.hom)
  let c : V ⟶ U := Over.homMk (pullback.fst d.left q.left) rfl
  let a : V ⟶ A := Over.homMk (pullback.snd d.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w d]
    rfl)
  refine ⟨V, c, a, ?_, ?_, ?_, Over.OverMorphism.ext pullback.condition⟩
  · change Flat (pullback.fst d.left q.left)
    infer_instance
  · change Surjective (pullback.fst d.left q.left)
    infer_instance
  · change LocallyOfFinitePresentation (pullback.fst d.left q.left)
    infer_instance

/-- To factor `y : U ⟶ X` through a monomorphism `m`, it suffices to factor it after
every base change along which a point `d : U ⟶ B` lifts through an fppf morphism
`q : A ⟶ B`. -/
theorem exists_factor_of_lift {A B U X Z : Over S} (q : A ⟶ B) [Flat q.left]
    [Surjective q.left] [LocallyOfFinitePresentation q.left] (m : Z ⟶ X) [Mono m]
    (d : U ⟶ B) (y : U ⟶ X)
    (h : ∀ (V : Over S) (c : V ⟶ U) (a : V ⟶ A), c ≫ d = a ≫ q →
      ∃ z : V ⟶ Z, z ≫ m = c ≫ y) :
    ∃ w : U ⟶ Z, w ≫ m = y := by
  obtain ⟨V, c, a, h₁, h₂, h₃, hca⟩ := exists_fppf_lift q d
  obtain ⟨z, hz⟩ := h V c a hca
  exact exists_factor_of_fppf c m y z hz

/-- Equality of two morphisms out of `T` can be tested after the base change along
which a point `x : T ⟶ Q` lifts through an fppf morphism `q : X ⟶ Q`. -/
theorem hom_ext_of_fppf_lift {X Q T Y : Over S} (q : X ⟶ Q) [Flat q.left]
    [Surjective q.left] [LocallyOfFinitePresentation q.left] (x : T ⟶ Q) (f g : T ⟶ Y)
    (h : ∀ (V : Over S) (v : V ⟶ T) (a : V ⟶ X), v ≫ x = a ≫ q → v ≫ f = v ≫ g) :
    f = g := by
  obtain ⟨V, v, a, h₁, h₂, h₃, hva⟩ := exists_fppf_lift q x
  have : Epi v := epi_of_fppf v
  exact (cancel_epi v).mp (h V v a hva)

/-- If `r` and the fppf morphism `q` have the same fibres on every relative test, the
morphism descended from `r` along `q` is a monomorphism of schemes. -/
theorem mono_desc_of_fppf_fiber_iff {X Q R : Over S} (q : X ⟶ Q) [Flat q.left]
    [Surjective q.left] [LocallyOfFinitePresentation q.left] (r : X ⟶ R)
    (h : ∀ (T : Over S) (a b : T ⟶ X), a ≫ q = b ≫ q ↔ a ≫ r = b ≫ r) :
    Mono (HomogeneousQuotientComparison.desc q r (fun T a b hab => (h T a b).mp hab)).left := by
  let d := HomogeneousQuotientComparison.desc q r (fun T a b hab => (h T a b).mp hab)
  have hd : q ≫ d = r := HomogeneousQuotientComparison.fac_desc q r _
  have : Mono d := by
    constructor
    intro T a b hab
    apply hom_ext_of_fppf_lift q a a b
    intro V v a' ha
    apply hom_ext_of_fppf_lift q (v ≫ b) (v ≫ a) (v ≫ b)
    intro W w b' hb
    have he : (w ≫ a') ≫ r = b' ≫ r := by
      calc
        (w ≫ a') ≫ r = w ≫ (a' ≫ q) ≫ d := by
          rw [← hd]
          simp only [Category.assoc]
        _ = w ≫ (v ≫ a) ≫ d := by rw [← ha]
        _ = w ≫ (v ≫ b) ≫ d := by
          simpa only [Category.assoc] using congrArg (fun z => w ≫ v ≫ z) hab
        _ = b' ≫ r := by
          rw [← hd]
          simpa only [Category.assoc] using congrArg (fun z => z ≫ d) hb
    have he' := (h W (w ≫ a') b').mpr he
    simpa only [Category.assoc, ← ha, ← hb] using he'
  exact Over.mono_left_of_mono d

end FppfDescent

section Normalizer

variable {S : Scheme.{u}} {G L : GroupScheme S} {T D : CommGroupScheme S}
  (ρ : G ⟶ L) (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp) (e : D.toGrp ⟶ L)

/-- **The preimage of the image torus.** Let `ρ : G ⟶ L` have central kernel, let `t`
represent its own centralizer, and let `t ≫ ρ = π ≫ e` with `π` fppf. A point `y` of
`G` with `ρ(y) = e(d)` for a point `d` of `D` is a point of `T`. -/
theorem exists_torus_point_of_comp_eq
    (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
    (hcent : (torusCentralizer t).IsRepresentedBy t)
    [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (hπe : π ≫ e = t ≫ ρ)
    {U : Over S} (y : U ⟶ G.X) (d : U ⟶ D.X) (hy : y ≫ ρ.hom.hom = d ≫ e.hom.hom) :
    ∃ τ : U ⟶ T.X, τ ≫ t.hom.hom = y := by
  have hπe' : π.hom.hom ≫ e.hom.hom = t.hom.hom ≫ ρ.hom.hom :=
    congrArg (fun φ => φ.hom.hom) hπe
  have : Mono t.hom.hom := hcent.1
  apply exists_factor_of_lift π.hom.hom t.hom.hom d y
  intro V c a hca
  let k : V ⟶ G.X := (c ≫ y) * (a ≫ t.hom.hom)⁻¹
  have h₁ : (c ≫ y) ≫ ρ.hom.hom = (a ≫ t.hom.hom) ≫ ρ.hom.hom := by
    rw [Category.assoc, hy, ← Category.assoc, hca, Category.assoc, hπe', Category.assoc]
  have hk : k ≫ ρ.hom.hom = 1 := by
    simp only [k, MonObj.mul_comp, GrpObj.inv_comp, h₁, mul_inv_cancel]
  have hkc : k ∈ (torusCentralizer t).carrier V := by
    intro W b σ
    exact hρ W (b ≫ k) (σ ≫ t.hom.hom) (by rw [Category.assoc, hk, MonObj.comp_one])
  rw [← hcent.2] at hkc
  obtain ⟨τ₁, hτ₁⟩ := SubgroupFunctor.mem_range.mp hkc
  refine ⟨τ₁ * a, ?_⟩
  rw [MonObj.mul_comp, hτ₁]
  simp only [k, inv_mul_cancel_right]

/-- Points of the normalizer of `T` map into the normalizer of the image torus. -/
theorem comp_mem_normalizer_of_mem_torusNormalizer
    [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (he : Mono e.hom.hom)
    (hπe : π ≫ e = t ≫ ρ) {U : Over S} {x : U ⟶ G.X}
    (hx : x ∈ (torusNormalizer t).carrier U) :
    x ≫ ρ.hom.hom ∈ (SubgroupFunctor.range e).normalizer.carrier U := by
  have hπe' : π.hom.hom ≫ e.hom.hom = t.hom.hom ≫ ρ.hom.hom :=
    congrArg (fun φ => φ.hom.hom) hπe
  intro V a y hy
  obtain ⟨d, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  constructor
  · obtain ⟨w, hw⟩ := exists_factor_of_lift π.hom.hom e.hom.hom d
      ((a ≫ x ≫ ρ.hom.hom) * (d ≫ e.hom.hom) * (a ≫ x ≫ ρ.hom.hom)⁻¹) (by
        intro W c b hcb
        obtain ⟨⟨τ', hτ'⟩, -⟩ := (mem_torusNormalizer t).mp hx W (c ≫ a) b
        have key : c ≫ d ≫ e.hom.hom = b ≫ t.hom.hom ≫ ρ.hom.hom := by
          rw [← Category.assoc, hcb, Category.assoc, hπe']
        refine ⟨τ' ≫ π.hom.hom, ?_⟩
        calc (τ' ≫ π.hom.hom) ≫ e.hom.hom = (τ' ≫ t.hom.hom) ≫ ρ.hom.hom := by
              rw [Category.assoc, hπe', Category.assoc]
          _ = (((c ≫ a) ≫ x) * (b ≫ t.hom.hom) * ((c ≫ a) ≫ x)⁻¹) ≫ ρ.hom.hom := by
              rw [hτ']
          _ = _ := by
              simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv,
                Category.assoc, key])
    exact SubgroupFunctor.mem_range.mpr ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := exists_factor_of_lift π.hom.hom e.hom.hom d
      ((a ≫ x ≫ ρ.hom.hom)⁻¹ * (d ≫ e.hom.hom) * (a ≫ x ≫ ρ.hom.hom)) (by
        intro W c b hcb
        obtain ⟨-, ⟨τ', hτ'⟩⟩ := (mem_torusNormalizer t).mp hx W (c ≫ a) b
        have key : c ≫ d ≫ e.hom.hom = b ≫ t.hom.hom ≫ ρ.hom.hom := by
          rw [← Category.assoc, hcb, Category.assoc, hπe']
        refine ⟨τ' ≫ π.hom.hom, ?_⟩
        calc (τ' ≫ π.hom.hom) ≫ e.hom.hom = (τ' ≫ t.hom.hom) ≫ ρ.hom.hom := by
              rw [Category.assoc, hπe', Category.assoc]
          _ = (((c ≫ a) ≫ x)⁻¹ * (b ≫ t.hom.hom) * ((c ≫ a) ≫ x)) ≫ ρ.hom.hom := by
              rw [hτ']
          _ = _ := by
              simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv,
                Category.assoc, key])
    exact SubgroupFunctor.mem_range.mpr ⟨w, hw⟩

/-- A point whose image normalizes the image torus normalizes `T`. -/
theorem mem_torusNormalizer_of_comp_mem_normalizer
    (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
    (hcent : (torusCentralizer t).IsRepresentedBy t)
    [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (hπe : π ≫ e = t ≫ ρ)
    {U : Over S} {x : U ⟶ G.X}
    (hx : x ≫ ρ.hom.hom ∈ (SubgroupFunctor.range e).normalizer.carrier U) :
    x ∈ (torusNormalizer t).carrier U := by
  have hπe' : π.hom.hom ≫ e.hom.hom = t.hom.hom ≫ ρ.hom.hom :=
    congrArg (fun φ => φ.hom.hom) hπe
  rw [mem_torusNormalizer]
  intro V a τ
  have hτ : τ ≫ t.hom.hom ≫ ρ.hom.hom ∈ (SubgroupFunctor.range e).carrier V :=
    SubgroupFunctor.mem_range.mpr ⟨τ ≫ π.hom.hom, by rw [Category.assoc, hπe']⟩
  obtain ⟨h₁, h₂⟩ := hx V a _ hτ
  obtain ⟨d₁, hd₁⟩ := SubgroupFunctor.mem_range.mp h₁
  obtain ⟨d₂, hd₂⟩ := SubgroupFunctor.mem_range.mp h₂
  constructor
  · obtain ⟨τ', hτ'⟩ := exists_torus_point_of_comp_eq ρ t π e hρ hcent hπe
      ((a ≫ x) * (τ ≫ t.hom.hom) * (a ≫ x)⁻¹) d₁ (by
        simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
        exact hd₁.symm)
    exact ⟨τ', hτ'.symm⟩
  · obtain ⟨τ', hτ'⟩ := exists_torus_point_of_comp_eq ρ t π e hρ hcent hπe
      ((a ≫ x)⁻¹ * (τ ≫ t.hom.hom) * (a ≫ x)) d₂ (by
        simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
        exact hd₂.symm)
    exact ⟨τ', hτ'.symm⟩

/-- **Fibres of the conjugacy map.** For the morphism `f` classifying the conjugates
`g ↦ ρ(g) D ρ(g)⁻¹` through a universal family of closed subtori of `L`, two points
of `G` have the same image under `f` exactly when they differ by a point of the
normalizer of `T`. -/
theorem comp_eq_iff_mem_torusNormalizer
    (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
    (hcent : (torusCentralizer t).IsRepresentedBy t)
    [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (he : Mono e.hom.hom)
    (hπe : π ≫ e = t ≫ ρ)
    {M : Over S} {K : GroupScheme M.left} (j : K ⟶ (GroupScheme.baseChange M.hom).obj L)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (huni : TorusSubgroupModuli.IsUniversal j) (f : G.X ⟶ M)
    (hf : TorusSubgroupModuli.evaluate j f =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e ρ.hom.hom))
    {U : Over S} (g h : U ⟶ G.X) :
    g ≫ f = h ≫ f ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U := by
  have hev : ∀ x : U ⟶ G.X, TorusSubgroupModuli.evaluate j (x ≫ f) =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e (x ≫ ρ.hom.hom)) := by
    intro x
    rw [← TorusSubgroupModuli.evaluate_comp,
      TorusSubgroupModuli.evaluate_eq_of_range_eq _ _ hf x]
    exact SubgroupFunctor.evaluate_conjugateFamily e ρ.hom.hom x
  have hinj : g ≫ f = h ≫ f ↔
      TorusSubgroupModuli.evaluate j (g ≫ f) = TorusSubgroupModuli.evaluate j (h ≫ f) := by
    refine ⟨fun hgh => by rw [hgh], fun hev' => ?_⟩
    obtain ⟨a, -, ha⟩ := huni U (TorusSubgroupModuli.evaluate j (g ≫ f))
      (TorusSubgroupModuli.isAdmissible_evaluate j hj hK _)
    exact (ha _ rfl).trans (ha _ hev'.symm).symm
  have hcomp : (g ≫ ρ.hom.hom)⁻¹ * (h ≫ ρ.hom.hom) = (g⁻¹ * h) ≫ ρ.hom.hom := by
    rw [MonObj.mul_comp, GrpObj.inv_comp]
  rw [hinj, hev, hev, SubgroupFunctor.range_conjugateFamily_eq_iff, hcomp]
  exact ⟨mem_torusNormalizer_of_comp_mem_normalizer ρ t π e hρ hcent hπe,
    comp_mem_normalizer_of_mem_torusNormalizer ρ t π e he hπe⟩

end Normalizer

section ConjugacyQuotientMap

variable {S : Scheme.{u}} {G L : GroupScheme S} {T D : CommGroupScheme S}
  {M : Over S} {K : GroupScheme M.left}

/-- **The conjugacy map out of the normalizer quotient.** With the data of
`comp_eq_iff_mem_torusNormalizer`, let `p : G.X ⟶ Y` be fppf with fibres exactly the
cosets of the normalizer of `T`. The conjugacy map `f` is constant on these fibres,
so it descends along `p` to `Y ⟶ M`, sending the class of `g` to the parameter of
`ρ(g) D ρ(g)⁻¹`. -/
def conjugacyQuotientMap (ρ : G ⟶ L) (t : T.toGrp ⟶ G) (π : T.toGrp ⟶ D.toGrp)
    (e : D.toGrp ⟶ L)
    (hρ : ∀ (U : Over S) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g)
    (hcent : (torusCentralizer t).IsRepresentedBy t)
    [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (he : Mono e.hom.hom)
    (hπe : π ≫ e = t ≫ ρ) (j : K ⟶ (GroupScheme.baseChange M.hom).obj L)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (huni : TorusSubgroupModuli.IsUniversal j) (f : G.X ⟶ M)
    (hf : TorusSubgroupModuli.evaluate j f =
      SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e ρ.hom.hom))
    {Y : Over S} (p : G.X ⟶ Y) [Flat p.left] [Surjective p.left]
    [LocallyOfFinitePresentation p.left]
    (hp : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U) : Y ⟶ M :=
  HomogeneousQuotientComparison.desc p f (fun U g h hgh =>
    (comp_eq_iff_mem_torusNormalizer ρ t π e hρ hcent he hπe j hj hK huni f hf g h).mpr
      ((hp U g h).mp hgh))

end ConjugacyQuotientMap

/-- **Reduction of the closed embedding to universal closedness.** The statement
`SelfCentralizingConjugacyUniversallyClosedStatement` implies
`SelfCentralizingConjugacyClosedEmbeddingStatement`. The conjugacy map descends along
the quotient map (`conjugacyQuotientMap`). The descended map is a monomorphism because
both maps have the same fibres (`comp_eq_iff_mem_torusNormalizer`), hence separated. It
is locally of finite type by descent along the fppf map `p`, and universally closed by
hypothesis. So it is a proper monomorphism, hence a closed immersion. -/
theorem selfCentralizingConjugacyClosedEmbedding_of_universallyClosed
    (hP : SelfCentralizingConjugacyUniversallyClosedStatement.{u}) :
    SelfCentralizingConjugacyClosedEmbeddingStatement.{u} := by
  intro R G hsm hsep hqc hfib m ρ hρ T t hT ht hmax hcent D π e hD he hπf hπs hπl hπe
    M K j hj hK huni f hf Y p hpf hps hpl hp
  have : Flat π.hom.hom.left := hπf
  have : Surjective π.hom.hom.left := hπs
  have : LocallyOfFinitePresentation π.hom.hom.left := hπl
  have : Flat p.left := hpf
  have : Surjective p.left := hps
  have : LocallyOfFinitePresentation p.left := hpl
  have : Smooth G.X.hom := hsm
  have : IsClosedImmersion e.hom.hom.left := he
  have he' : Mono e.hom.hom := Over.mono_of_mono_left _
  have hfib' : ∀ (U : Over (Spec R)) (g h : U ⟶ G.X), g ≫ p = h ≫ p ↔ g ≫ f = h ≫ f :=
    fun U g h => (hp U g h).trans
      (comp_eq_iff_mem_torusNormalizer ρ t π e hρ hcent he' hπe j hj hK huni f hf g h).symm
  let φ : Y ⟶ M :=
    conjugacyQuotientMap ρ t π e hρ hcent he' hπe j hj hK huni f hf p hp
  have hφ : p ≫ φ = f := HomogeneousQuotientComparison.fac_desc p f _
  have hmono : Mono φ.left := mono_desc_of_fppf_fiber_iff p f hfib'
  have huc : UniversallyClosed φ.left :=
    hP R G hsm hsep hqc hfib m ρ hρ T t hT ht hmax hcent D π e hD he hπf hπs hπl hπe
      M K j hj hK huni f hf Y p hpf hps hpl hp φ hφ
  have hf_lft : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ M.hom) := by
      rw [Over.w f]
      infer_instance
    exact locallyOfFiniteType_of_comp f.left M.hom
  have hlft : LocallyOfFiniteType φ.left := by
    refine Langlands.AlgebraicGeometry.locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp
      _ _ _ p.left φ.left hps hpf hpl ?_
    rw [← Over.comp_left, hφ]
    exact hf_lft
  have hprop : IsProper φ.left := by
    have : UniversallyClosed φ.left := huc
    have : LocallyOfFiniteType φ.left := hlft
    exact ⟨⟩
  exact ⟨φ, hφ, (IsClosedImmersion.iff_isProper_and_mono φ.left).mpr ⟨hprop, hmono⟩⟩

end SelfCentralizingConjugacyClosedEmbeddingReduction

end Langlands.GroupScheme
