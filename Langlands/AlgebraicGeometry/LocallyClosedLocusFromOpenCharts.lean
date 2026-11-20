import Langlands.AlgebraicGeometry.ClosedLocusFromDirectedCover

/-! # Locally closed loci from closed representatives over base opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ S) → Prop)

/-- On a base open, the property is given by factorization through a closed immersion. -/
def HasClosedOpenChart (U : S.Opens) : Prop :=
  ∃ (Z : Scheme.{u}) (j : Z ⟶ U.toScheme), IsClosedImmersion j ∧
    ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
      (∃ k : T ⟶ Z, k ≫ j = g) ↔ P (g ≫ U.ι)

/-- Closed representatives on open neighborhoods of the images of all points of
satisfying tests glue to a closed representative over one open of the base. -/
def LocallyClosedLocusFromOpenChartsStatement : Prop :=
  ∀ (S : Scheme.{u}) (P : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ S) → Prop),
    (∀ ⦃T T' : Scheme.{u}⦄ (b : T' ⟶ T) (g : T ⟶ S), P g → P (b ≫ g)) →
    (∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (𝒰 : T.OpenCover.{u}),
      (∀ i, P (𝒰.f i ≫ g)) → P g) →
    (∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), P g → ∀ t : T,
      ∃ U : S.Opens, g t ∈ U ∧ HasClosedOpenChart P U) →
      ∃ (U : S.Opens) (Z : Scheme.{u}) (j : Z ⟶ U.toScheme), IsClosedImmersion j ∧
        ∀ (T : Scheme.{u}) (g : T ⟶ S),
          (∃ k : T ⟶ Z, k ≫ j ≫ U.ι = g) ↔ P g

theorem locallyClosedLocus_of_openCharts : LocallyClosedLocusFromOpenChartsStatement.{u} := by
  intro S P hcomp hloc hcharts
  classical
  let C := {U : S.Opens // HasClosedOpenChart P U}
  let V : S.Opens := ⨆ c : C, c.1
  let I := {U : V.toScheme.Opens // ∃ c : C, U ≤ V.ι ⁻¹ᵁ c.1}
  have hb (x : V.toScheme) : ∃ c : C, x ∈ V.ι ⁻¹ᵁ c.1 := by
    change ∃ c : C, x.val ∈ c.1
    exact Opens.mem_iSup.mp x.property
  have hcov : IsOpenCover (fun i : I => i.1) := by
    apply top_unique
    intro x _
    obtain ⟨c, hc⟩ := hb x
    exact Opens.mem_iSup.mpr ⟨⟨V.ι ⁻¹ᵁ c.1, ⟨c, le_rfl⟩⟩, hc⟩
  let 𝒰 := V.toScheme.openCoverOfIsOpenCover (fun i : I => i.1) hcov
  let : Preorder 𝒰.I₀ := inferInstanceAs (Preorder I)
  have hR (i : 𝒰.I₀) : (𝒰.f i).opensRange = i.1 := Scheme.Opens.opensRange_ι _
  let : 𝒰.LocallyDirected := Scheme.Cover.LocallyDirected.ofIsBasisOpensRange
    (by intro i j; rw [hR i, hR j]; rfl) <| by
      apply Opens.isBasis_iff_nbhd.mpr
      intro W x hx
      obtain ⟨c, hc⟩ := hb x
      let i : I := ⟨W ⊓ V.ι ⁻¹ᵁ c.1, ⟨c, inf_le_right⟩⟩
      exact ⟨i.1, ⟨i, hR i⟩, ⟨hx, hc⟩, inf_le_left⟩
  let c (i : I) : C := i.property.choose
  have hc (i : I) : i.1 ≤ V.ι ⁻¹ᵁ (c i).1 := i.property.choose_spec
  let Z (i : I) : Scheme.{u} := (c i).property.choose
  let j (i : I) : Z i ⟶ (c i).1.toScheme := (c i).property.choose_spec.choose
  have hj (i : I) : IsClosedImmersion (j i) := (c i).property.choose_spec.choose_spec.1
  have hP (i : I) (T : Scheme.{u}) (g : T ⟶ (c i).1.toScheme) :
      (∃ k : T ⟶ Z i, k ≫ j i = g) ↔ P (g ≫ (c i).1.ι) :=
    (c i).property.choose_spec.choose_spec.2 T g
  let l (i : I) : (𝒰.X i) ⟶ (c i).1.toScheme :=
    IsOpenImmersion.lift (c i).1.ι (𝒰.f i ≫ V.ι) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hc i x.property)
  have hl (i : I) : l i ≫ (c i).1.ι = 𝒰.f i ≫ V.ι := IsOpenImmersion.lift_fac _ _ _
  let PV : ∀ ⦃T : Scheme.{u}⦄, (T ⟶ V.toScheme) → Prop := fun {_} g => P (g ≫ V.ι)
  let D : ClosedLocusFromDirectedCover.Data PV 𝒰 := {
    Z := fun i => pullback (j i) (l i)
    ι := fun i => pullback.snd (j i) (l i)
    closed := fun i => by
      have : IsClosedImmersion (j i) := hj i
      infer_instance
    chart_iff := by
      intro i T g
      change (∃ k : T ⟶ pullback (j i) (l i), k ≫ pullback.snd _ _ = g) ↔
        P ((g ≫ 𝒰.f i) ≫ V.ι)
      rw [Category.assoc, ← hl i, ← Category.assoc, ← hP i T (g ≫ l i)]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, hk]⟩
      · rintro ⟨k, hk⟩
        exact ⟨pullback.lift k g hk, pullback.lift_snd _ _ _⟩ }
  have hcomp' : ∀ ⦃T T' : Scheme.{u}⦄ (b : T' ⟶ T) (g : T ⟶ V.toScheme),
      PV g → PV (b ≫ g) := by
    intro T T' b g hg
    change P ((b ≫ g) ≫ V.ι)
    rw [Category.assoc]
    exact hcomp b (g ≫ V.ι) hg
  have hloc' : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ V.toScheme),
      (∀ i : 𝒰.I₀, PV ((𝒰.pullback₁ g : T.OpenCover).f i ≫ g)) → PV g := by
    intro T g hg
    apply hloc (g ≫ V.ι) (𝒰.pullback₁ g)
    intro i
    simpa only [PV, Category.assoc] using hg i
  refine ⟨V, D.scheme hcomp', D.inclusion hcomp', inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨k, hk⟩
    have h := (D.factors_iff hcomp' hloc' (k ≫ D.inclusion hcomp')).mp ⟨k, rfl⟩
    change P ((k ≫ D.inclusion hcomp') ≫ V.ι) at h
    rwa [Category.assoc, hk] at h
  · intro hg
    have hv : Set.range g ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      obtain ⟨U, ht, hu⟩ := hcharts g hg t
      exact Opens.mem_iSup.mpr ⟨⟨U, hu⟩, ht⟩
    let b := IsOpenImmersion.lift V.ι g hv
    have hb' : b ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
    have hPb : PV b := by change P (b ≫ V.ι); rwa [hb']
    obtain ⟨k, hk⟩ := (D.factors_iff hcomp' hloc' b).mpr hPb
    exact ⟨k, by rw [← Category.assoc, hk, hb']⟩

end Langlands.AlgebraicGeometry
