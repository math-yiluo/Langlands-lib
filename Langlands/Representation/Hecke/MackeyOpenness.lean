import Langlands.Representation.Hecke.MackeyModels
import Langlands.Representation.Hecke.HomomorphismLeft
import Langlands.Representation.Hecke.TestFunction
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Restriction and the smooth Hom bifunctor

Supporting results for the tensor identity of Renard III.2.11 (printed pp.82–83 /
PDF pp.88–89). A left adjoint of restriction along `φ : H →* G` forces every
`φ(U)`, for `U` an open subgroup of `H`, to contain an open subgroup of `G`; under
that condition the smooth part of the conjugation Hom commutes with restriction.
-/

noncomputable section

open CategoryTheory Pointwise

namespace Langlands.Hecke.Homomorphism

universe uG uH v

section QuotientRep

variable {G : Type uG} [Group G] (S : Subgroup G)

/-- Left translation on finitely supported functions on `G ⧸ S`. -/
def quotientRep : Representation ℂ G (G ⧸ S →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (fun c : G ⧸ S => g • c)
  map_one' := by
    refine Finsupp.lhom_ext fun c a => ?_
    simp
  map_mul' g g' := by
    refine Finsupp.lhom_ext fun c a => ?_
    simp [mul_smul]

theorem quotientRep_single (g : G) (c : G ⧸ S) (a : ℂ) :
    quotientRep S g (Finsupp.single c a) = Finsupp.single (g • c) a :=
  Finsupp.mapDomain_single

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The orbit map `gS ↦ g • x` of an `S`-fixed vector `x`. -/
def orbitMap (x : V) (hx : ∀ s ∈ S, ρ s x = x) : G ⧸ S → V := fun c =>
  Quotient.liftOn' c (fun g => ρ g x) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    calc ρ a x = ρ a (ρ (a⁻¹ * b) x) := by rw [hx _ hab]
      _ = ρ b x := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem orbitMap_mk (x : V) (hx : ∀ s ∈ S, ρ s x = x) (g : G) :
    orbitMap S ρ x hx (g : G ⧸ S) = ρ g x := rfl

theorem orbitMap_smul (x : V) (hx : ∀ s ∈ S, ρ s x = x) (g : G) (c : G ⧸ S) :
    orbitMap S ρ x hx (g • c) = ρ g (orbitMap S ρ x hx c) := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective c
  change ρ (g * g') x = ρ g (ρ g' x)
  rw [map_mul, Module.End.mul_apply]

/-- The equivariant map `ℂ[G/S] → V` sending `δ_{gS}` to `g • x`. -/
def quotientLift (x : V) (hx : ∀ s ∈ S, ρ s x = x) : (quotientRep S).IntertwiningMap ρ where
  toLinearMap := Finsupp.linearCombination ℂ (orbitMap S ρ x hx)
  isIntertwining' g := Finsupp.lhom_ext fun c a => by
    simp only [LinearMap.comp_apply, quotientRep_single, Finsupp.linearCombination_single,
      orbitMap_smul, map_smul]

theorem quotientLift_single_one (x : V) (hx : ∀ s ∈ S, ρ s x = x) :
    quotientLift S ρ x hx (Finsupp.single ((1 : G) : G ⧸ S) 1) = x := by
  change Finsupp.linearCombination ℂ (orbitMap S ρ x hx)
    (Finsupp.single ((1 : G) : G ⧸ S) 1) = x
  rw [Finsupp.linearCombination_single, one_smul, orbitMap_mk, map_one, Module.End.one_apply]

end QuotientRep

section AlgebraicPullback

variable {G : Type uG} [Group G] {H : Type uH} [Group H] (φ : H →* G)

/-- The vector `δ_{φ(U)}` of `ℂ[G/φ(U)]` is fixed by `U`. -/
theorem quotientRep_fixed (U : Subgroup H) {u : H} (hu : u ∈ U) :
    quotientRep (U.map φ) (φ u) (Finsupp.single ((1 : G) : G ⧸ U.map φ) 1) =
      Finsupp.single ((1 : G) : G ⧸ U.map φ) 1 := by
  rw [quotientRep_single]
  congr 1
  change ((φ u * 1 : G) : G ⧸ U.map φ) = ((1 : G) : G ⧸ U.map φ)
  rw [QuotientGroup.eq, mul_one, mul_one]
  exact U.map φ |>.inv_mem ⟨u, hu, rfl⟩

/-- The conjugation Hom commutes with pulling back along `φ`. -/
theorem linHom_comp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (Representation.linHom ρ σ).comp φ = Representation.linHom (ρ.comp φ) (σ.comp φ) :=
  MonoidHom.ext fun h => LinearMap.ext fun f => LinearMap.ext fun w => by
    simp [Representation.linHom_apply, map_inv]

end AlgebraicPullback

section Smoothness

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] (φ : H →* G)

/-- Smoothness for `ρ ∘ φ` gives smoothness for `ρ` once every `φ(U)`, `U` open in
`H`, contains an open subgroup of `G`. -/
theorem isSmoothVector_of_comp
    (hopen : ∀ U : OpenSubgroup H, ∃ K : OpenSubgroup G, ∀ k ∈ K, ∃ u ∈ U, φ u = k)
    {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {w : V}
    (hw : IsSmoothVector (ρ.comp φ) w) : IsSmoothVector ρ w := by
  obtain ⟨U, hU⟩ := hw
  obtain ⟨K, hK⟩ := hopen U
  refine ⟨K, ?_⟩
  change ∀ k : K, ρ (k : G) w = w
  intro k
  obtain ⟨u, hu, huk⟩ := hK k k.2
  rw [← huk]
  exact hU ⟨u, hu⟩

end Smoothness

section Fixing

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  (φ : H →* G) (hφ : Continuous φ)

/-- The image of a fixed vector under the unit of an adjunction `P ⊣ restriction`
yields one open subgroup of `G` fixing the image of that vector under every map. -/
theorem exists_fixing_of_adjunction
    {P : SmoothRep.{0, uH, max uG v} ℂ H ⥤ SmoothRep.{0, uG, max uG v} ℂ G}
    (adj : P ⊣ restriction.{uG, uH, max uG v} φ hφ) (W : SmoothRep.{0, uH, max uG v} ℂ H)
    (w : W) :
    ∃ K : OpenSubgroup G, ∀ (E : SmoothRep.{0, uG, max uG v} ℂ G)
      (f : W ⟶ (restriction.{uG, uH, max uG v} φ hφ).obj E), ∀ k ∈ K,
        E.representation k (SmoothRep.hom f w) = SmoothRep.hom f w := by
  obtain ⟨K, hK⟩ := (P.obj W).isSmooth (SmoothRep.hom (adj.unit.app W) w)
  refine ⟨K, fun E f k hk => ?_⟩
  have hf : f = adj.unit.app W ≫
      (restriction.{uG, uH, max uG v} φ hφ).map ((adj.homEquiv W E).symm f) :=
    ((adj.homEquiv W E).apply_symm_apply f).symm
  rw [hf]
  let g' := SmoothRep.hom ((adj.homEquiv W E).symm f)
  let r : P.obj W := SmoothRep.hom (adj.unit.app W) w
  change E.representation k (g' r) = g' r
  calc E.representation k (g' r) = g' ((P.obj W).representation k r) :=
        (Representation.IntertwiningMap.isIntertwining _ _ g' k r).symm
    _ = g' r := congrArg g' (hK ⟨k, hk⟩)

end Fixing

section Openness

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  (φ : H →* G) (hφ : Continuous φ)

/-- The `H`-smooth vectors of `ℂ[G/S]`, with `H` acting through `φ`, lifted to the
carrier universe `max uG v`. -/
abbrev quotientTestObj (S : Subgroup G) : SmoothRep.{0, uH, max uG v} ℂ H :=
  MixedProductTensor.liftObj.{uH, uG, max uG v}
    (SmoothRep.smoothPartObj ℂ H (Rep.of ((quotientRep S).comp φ)))

/-- The vector `δ_{φ(U)}`, which is fixed by `U`. -/
def quotientBase (U : OpenSubgroup H) : quotientTestObj.{uG, uH, v} φ (U.toSubgroup.map φ) :=
  ULift.up ⟨Finsupp.single ((1 : G) : G ⧸ U.toSubgroup.map φ) 1,
    ⟨U, fun u => quotientRep_fixed φ U.toSubgroup u.2⟩⟩

/-- An `H`-map out of `quotientTestObj` sending the base vector to a given
`φ(U)`-fixed vector. -/
def quotientTestHom (U : OpenSubgroup H) (E : SmoothRep.{0, uG, max uG v} ℂ G) (x : E)
    (hx : ∀ s ∈ U.toSubgroup.map φ, E.representation s x = x) :
    quotientTestObj.{uG, uH, v} φ (U.toSubgroup.map φ) ⟶
      (restriction.{uG, uH, max uG v} φ hφ).obj E :=
  SmoothRep.ofHom
    { toLinearMap := (quotientLift _ E.representation x hx).toLinearMap ∘ₗ
        (smoothVectors _).subtype ∘ₗ ULift.moduleEquiv.toLinearMap
      isIntertwining' := fun h => LinearMap.ext fun w =>
        Representation.IntertwiningMap.isIntertwining _ _
          (quotientLift _ E.representation x hx) (φ h) w.down.val }

theorem quotientTestHom_base (U : OpenSubgroup H) (E : SmoothRep.{0, uG, max uG v} ℂ G)
    (x : E) (hx : ∀ s ∈ U.toSubgroup.map φ, E.representation s x = x) :
    SmoothRep.hom (quotientTestHom φ hφ U E x hx) (quotientBase φ U) = x := by
  change quotientLift _ E.representation x hx
    (Finsupp.single ((1 : G) : G ⧸ U.toSubgroup.map φ) 1) = x
  exact quotientLift_single_one _ E.representation x hx

variable [T2Space G] [NonarchimedeanGroup G] [LocallyCompactSpace G] [LocallyCompactSpace H]

/-- A left adjoint of restriction along `φ` forces `φ(U)` to contain an open subgroup
of `G` for every open subgroup `U` of `H`. -/
theorem exists_openSubgroup_le_map_of_adjunction
    {P : SmoothRep.{0, uH, max uG v} ℂ H ⥤ SmoothRep.{0, uG, max uG v} ℂ G}
    (adj : P ⊣ restriction.{uG, uH, max uG v} φ hφ) (U : OpenSubgroup H) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∃ u ∈ U, φ u = k := by
  classical
  obtain ⟨U₀, hU₀c, hU₀U⟩ := compactOpenSubgroupBasis H (U : Set H) U.mem_nhds_one
  obtain ⟨K, hK⟩ := exists_fixing_of_adjunction φ hφ adj
    (quotientTestObj.{uG, uH, v} φ (U₀.toSubgroup.map φ)) (quotientBase φ U₀)
  have hSdef : ((U₀.toSubgroup.map φ : Subgroup G) : Set G) = φ '' (U₀ : Set H) :=
    Subgroup.coe_map _ _
  refine ⟨K, fun g hg => ?_⟩
  by_contra hne
  have hgS : g ∉ U₀.toSubgroup.map φ := by
    rintro ⟨u, hu, hug⟩
    exact hne ⟨u, hU₀U hu, hug⟩
  have hSc : IsCompact ((U₀.toSubgroup.map φ : Subgroup G) : Set G) := by
    rw [hSdef]
    exact hU₀c.image hφ
  have hC : IsClosed ((fun s => s * g) '' ((U₀.toSubgroup.map φ : Subgroup G) : Set G)) :=
    (hSc.image (continuous_mul_const g)).isClosed
  have h1 : (1 : G) ∉ (fun s => s * g) '' ((U₀.toSubgroup.map φ : Subgroup G) : Set G) := by
    rintro ⟨s, hs, hsg⟩
    apply hgS
    rw [eq_inv_of_mul_eq_one_right hsg]
    exact (U₀.toSubgroup.map φ).inv_mem hs
  obtain ⟨K', hK'c, hK'⟩ :=
    compactOpenSubgroupBasis G _ (hC.isOpen_compl.mem_nhds h1)
  set A : Set G := ((U₀.toSubgroup.map φ : Subgroup G) : Set G) * (K' : Set G) with hAdef
  have hAo : IsOpen A := K'.isOpen.mul_left
  have hAc : IsCompact A := hSc.mul hK'c
  have hmemA : ∀ s ∈ U₀.toSubgroup.map φ, ∀ y, y ∈ A → s * y ∈ A := by
    rintro s hs y ⟨t, ht, k, hk, rfl⟩
    exact ⟨s * t, (U₀.toSubgroup.map φ).mul_mem hs ht, k, hk, mul_assoc _ _ _⟩
  have hiff : ∀ s ∈ U₀.toSubgroup.map φ, ∀ y, s * y ∈ A ↔ y ∈ A := fun s hs y =>
    ⟨fun h => by simpa using hmemA s⁻¹ ((U₀.toSubgroup.map φ).inv_mem hs) _ h, hmemA s hs y⟩
  let χ : HarmonicAnalysis.SchwartzBruhat G :=
    TestFunction.characteristic ⟨hAc.isClosed, hAo⟩ hAc
  let E : SmoothRep.{0, uG, max uG v} ℂ G :=
    MixedProductTensor.liftObj.{uG, uG, max uG v}
      (SmoothRep.of (HarmonicAnalysis.GroupAction.leftTests (G := G)) isSmooth_leftTests)
  have hχ : ∀ s ∈ U₀.toSubgroup.map φ, E.representation s (ULift.up χ) = ULift.up χ := by
    intro s hs
    apply congrArg ULift.up
    apply TestFunction.ext
    intro y
    change A.indicator (fun _ => (1 : ℂ)) (s⁻¹ * y) = A.indicator (fun _ => (1 : ℂ)) y
    simp only [Set.indicator_apply, hiff s⁻¹ ((U₀.toSubgroup.map φ).inv_mem hs) y]
  have hfix : E.representation g (ULift.up χ) = ULift.up χ := by
    have h := hK E (quotientTestHom φ hφ U₀ E (ULift.up χ) hχ) g hg
    rwa [quotientTestHom_base φ hφ U₀ E (ULift.up χ) hχ] at h
  have h2 : χ (g⁻¹ * g) = χ g :=
    congrArg (fun y : ULift (HarmonicAnalysis.SchwartzBruhat G) => y.down g) hfix
  rw [inv_mul_cancel] at h2
  have h1A : (1 : G) ∈ A := ⟨1, (U₀.toSubgroup.map φ).one_mem, 1, K'.one_mem, one_mul 1⟩
  have hgA : g ∈ A := by
    by_contra hgA
    change A.indicator (fun _ => (1 : ℂ)) 1 = A.indicator (fun _ => (1 : ℂ)) g at h2
    simp only [Set.indicator_apply, h1A, hgA, ite_true, ite_false] at h2
    exact one_ne_zero h2
  obtain ⟨s, hs, k, hk, hsk⟩ := hgA
  apply hK' hk
  refine ⟨s⁻¹, (U₀.toSubgroup.map φ).inv_mem hs, ?_⟩
  change s⁻¹ * g = k
  rw [← show s * k = g from hsk, inv_mul_cancel_left]

end Openness

section HomComparison

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] (φ : H →* G)

/-- `G`-smooth linear maps stay smooth for the conjugation action through `φ`. -/
theorem smoothVectors_linHom_le (hφ : Continuous φ) {V W : Type*} [AddCommGroup V]
    [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    smoothVectors (Representation.linHom ρ σ) ≤
      smoothVectors (Representation.linHom (ρ.comp φ) (σ.comp φ)) := fun f hf => by
  change IsSmoothVector _ f
  rw [← linHom_comp]
  exact isSmoothVector_comp φ hφ hf

/-- Under the openness condition, smooth linear maps for the action through `φ` are
`G`-smooth. -/
theorem smoothVectors_linHom_ge
    (hopen : ∀ U : OpenSubgroup H, ∃ K : OpenSubgroup G, ∀ k ∈ K, ∃ u ∈ U, φ u = k)
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    smoothVectors (Representation.linHom (ρ.comp φ) (σ.comp φ)) ≤
      smoothVectors (Representation.linHom ρ σ) := fun f hf => by
  apply isSmoothVector_of_comp φ hopen
  rw [linHom_comp]
  exact hf

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Under the openness condition, restriction commutes with the smooth Hom bifunctor;
each component is the identity on linear maps. -/
def restrictionHomIso (hφ : Continuous φ)
    (hopen : ∀ U : OpenSubgroup H, ∃ K : OpenSubgroup G, ∀ k ∈ K, ∃ u ∈ U, φ u = k) :
    smoothHomBifunctor.{uG, v} G ⋙ restriction.{uG, uH, v} φ hφ ≅
      (restriction.{uG, uH, v} φ hφ).op.prod (restriction.{uG, uH, v} φ hφ) ⋙
        smoothHomBifunctor.{uH, v} H :=
  NatIso.ofComponents
    (fun X =>
      { hom := SmoothRep.ofHom
          { toLinearMap := Submodule.inclusion
              (smoothVectors_linHom_le φ hφ X.1.unop.representation X.2.representation)
            isIntertwining' := fun h => LinearMap.ext fun f => Subtype.ext <|
              congrArg (fun r : Representation ℂ H (X.1.unop →ₗ[ℂ] X.2) => r h f.1)
                (linHom_comp φ X.1.unop.representation X.2.representation) }
        inv := SmoothRep.ofHom
          { toLinearMap := Submodule.inclusion
              (smoothVectors_linHom_ge φ hopen X.1.unop.representation X.2.representation)
            isIntertwining' := fun h => LinearMap.ext fun f => Subtype.ext <|
              (congrArg (fun r : Representation ℂ H (X.1.unop →ₗ[ℂ] X.2) => r h f.1)
                (linHom_comp φ X.1.unop.representation X.2.representation)).symm }
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

end HomComparison

end Langlands.Hecke.Homomorphism
