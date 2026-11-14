import Langlands.Representation.CuspidalSupport.InducedKernelVanishing
import Langlands.Representation.Filtration.CommutingHomDevissage
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof

/-! # Central endomorphisms of `i_P σ` induced from `σ`

Let `σ` be a supercuspidal representation of `M(F)` with no nonzero vector fixed by an element
none of whose positive powers lies in `⁰M(F)`, and let `ζ` be central in `End(σ)`. Suppose `ζ`
commutes with every linear map `T : σ → σ` that is twisted-equivariant along the conjugation
of `M` by an element of `G(F)` normalizing it. Then `i_P(ζ)` is central in `End(i_P σ)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v uH uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Generic

variable {R : Type*} {H : Type*} [CommRing R] [Monoid H] {C : Type*} [Category C]

/-- An identity `A(a) ≫ g = g ≫ β` for all maps out of `B X` transfers along `A ≅ B`. -/
theorem map_comp_eq_comp_of_iso {A B : C ⥤ Rep R H} (α : A ≅ B) {X : C} {Y : Rep R H}
    (a : X ⟶ X) (β : Y ⟶ Y) (h : ∀ g : B.obj X ⟶ Y, B.map a ≫ g = g ≫ β)
    (g : A.obj X ⟶ Y) : A.map a ≫ g = g ≫ β := by
  have h1 := h (α.inv.app X ≫ g)
  have h2 : A.map a ≫ α.hom.app X = α.hom.app X ≫ B.map a := α.hom.naturality a
  calc A.map a ≫ g = A.map a ≫ α.hom.app X ≫ α.inv.app X ≫ g := by
        rw [Iso.hom_inv_id_app_assoc]
    _ = α.hom.app X ≫ B.map a ≫ α.inv.app X ≫ g := by rw [reassoc_of% h2]
    _ = α.hom.app X ≫ (α.inv.app X ≫ g) ≫ β := by rw [h1]
    _ = g ≫ β := by simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Maps out of `A X` vanish when `A ≅ B` and `B X` is zero. -/
theorem eq_zero_of_iso_subsingleton {A B : C ⥤ Rep R H} (α : A ≅ B) {X : C} {Y : Rep R H}
    (hB : Subsingleton (B.obj X)) (g : A.obj X ⟶ Y) : g = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  have h1 : y = (α.app X).inv.hom ((α.app X).hom.hom y) :=
    (Rep.inv_hom_apply (A := A.obj X) (B := B.obj X) (α.app X) y).symm
  rw [h1, Subsingleton.elim ((α.app X).hom.hom y) 0, map_zero, map_zero]
  rfl

/-- Being central is preserved and reflected by a group isomorphism. -/
theorem mulEquiv_apply_mem_center_iff {A B F : Type*} [Group A] [Group B] [EquivLike F A B]
    [MulEquivClass F A B] (ψ : F) (x : A) :
    ψ x ∈ Subgroup.center B ↔ x ∈ Subgroup.center A := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply EquivLike.injective ψ
    rw [map_mul, map_mul, h]
  · intro h g
    obtain ⟨g, rfl⟩ := EquivLike.surjective ψ g
    rw [← map_mul, ← map_mul, h]

/-- The action of a central element as an endomorphism of a smooth representation. -/
def centerEndomorphism {K : Type uH} [Group K] [TopologicalSpace K]
    (σ : SmoothRep.{0, uH, uW} ℂ K) (c : K) (hc : c ∈ Subgroup.center K) : σ ⟶ σ :=
  SmoothRep.ofHom ⟨σ.representation c, fun m => LinearMap.ext fun v => by
    change σ.representation c (σ.representation m v) = σ.representation m (σ.representation c v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      Subgroup.mem_center_iff.mp hc m]⟩

theorem centerEndomorphism_apply {K : Type uH} [Group K] [TopologicalSpace K]
    (σ : SmoothRep.{0, uH, uW} ℂ K) (c : K) (hc : c ∈ Subgroup.center K) (v : σ) :
    SmoothRep.hom (centerEndomorphism σ c hc) v = σ.representation c v := rfl

end Generic

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedCenterCriterionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
set_option maxHeartbeats 800000 in
/-- On a full piece of the geometric lemma for `r_P ∘ i_P`, every map to `σ` intertwines the
piece of `ζ` with `ζ`, provided `ζ` commutes with the linear maps `σ → σ` that are
twisted-equivariant along the conjugation recovered from the piece. -/
theorem fullPiece_hom_comm_of_twisted {z : rationalPoints G}
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
    [IsIso D.p'] [IsIso D.q']
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (ζ : letI := leviPointTopology l hl; σ ⟶ σ)
    (hζ : letI := leviPointTopology l hl
      ∀ T : σ →ₗ[ℂ] σ, (∀ (m : rationalPoints M) (v : σ),
          T (σ.representation m v) =
            σ.representation (rationalPoints.map D.fullLeviConjugacy.val.hom m) (T v)) →
        ∀ v : σ, T (SmoothRep.hom ζ v) = SmoothRep.hom ζ (T v))
    (g : letI := leviPointTopology l hl; D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ) :
    letI := leviPointTopology l hl
    D.pieceFunctor.map ζ ≫ g = g ≫ SmoothRep.toRep.map ζ := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let ψ := D.fullLeviPointsEquiv
  let E := D.fullPieceEquiv σ
  let T : σ →ₗ[ℂ] σ := g.hom.toLinearMap ∘ₗ E.symm.toIntertwiningMap.toLinearMap
  have hT (v : σ) : T v = g.hom (E.symm v) := rfl
  have hTtwist (m : rationalPoints M) (v : σ) :
      T (σ.representation m v) =
        σ.representation (rationalPoints.map D.fullLeviConjugacy.val.hom m) (T v) := by
    rw [hT, hT, ← D.fullLeviPointsEquiv_apply]
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap
      (ψ m) v
    change E.symm (σ.representation (ψ.symm (ψ m)) v) = _ at h1
    rw [ψ.symm_apply_apply] at h1
    rw [h1]
    exact Rep.hom_comm_apply g (ψ m) _
  have hTζ := hζ T hTtwist
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  have h1 : (D.pieceFunctor.map ζ).hom y = E.symm (SmoothRep.hom ζ (E y)) := by
    have h0 := D.fullPieceEquiv_naturality ζ y
    change E ((D.pieceFunctor.map ζ).hom y) = SmoothRep.hom ζ (E y) at h0
    rw [← h0, Representation.Equiv.symm_apply_apply]
  change g.hom ((D.pieceFunctor.map ζ).hom y) = SmoothRep.hom ζ (g.hom y)
  rw [h1]
  have h2 := hTζ (E y)
  rw [hT, hT, Representation.Equiv.symm_apply_apply] at h2
  exact h2

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
set_option maxHeartbeats 800000 in
/-- On a full piece of the geometric lemma for `r_P ∘ i_P`, with recovered point equivalence
`ψ`, a central `c` of `M(F)` acts as `ψ(c)` does on the target: every map `g` to `σ` satisfies
`g ∘ piece(σ(c)) = σ(ψ c) ∘ g`. -/
theorem fullPiece_hom_comm_center {z : rationalPoints G}
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
    [IsIso D.p'] [IsIso D.q']
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (c : rationalPoints M) (hc : c ∈ Subgroup.center (rationalPoints M))
    (hψc : D.fullLeviPointsEquiv c ∈ Subgroup.center (rationalPoints M))
    (g : letI := leviPointTopology l hl; D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ) :
    letI := leviPointTopology l hl
    D.pieceFunctor.map (centerEndomorphism σ c hc) ≫ g =
      g ≫ SmoothRep.toRep.map (centerEndomorphism σ (D.fullLeviPointsEquiv c) hψc) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let ψ := D.fullLeviPointsEquiv
  let E := D.fullPieceEquiv σ
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  have h1 : (D.pieceFunctor.map (centerEndomorphism σ c hc)).hom y =
      E.symm (σ.representation c (E y)) := by
    have h0 := D.fullPieceEquiv_naturality (centerEndomorphism σ c hc) y
    change E ((D.pieceFunctor.map (centerEndomorphism σ c hc)).hom y) =
      σ.representation c (E y) at h0
    rw [← h0, Representation.Equiv.symm_apply_apply]
  have h2 : (D.pieceFunctor.obj σ).ρ (ψ c) y = E.symm (σ.representation c (E y)) := by
    have h3 := Representation.IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap
      (ψ c) (E y)
    change E.symm (σ.representation (ψ.symm (ψ c)) (E y)) =
      (D.pieceFunctor.obj σ).ρ (ψ c) (E.symm (E y)) at h3
    rw [ψ.symm_apply_apply, Representation.Equiv.symm_apply_apply] at h3
    exact h3.symm
  change g.hom ((D.pieceFunctor.map (centerEndomorphism σ c hc)).hom y) =
    σ.representation (ψ c) (g.hom y)
  rw [h1, ← h2]
  exact Rep.hom_comm_apply g (ψ c) y

omit [T2Space k] in
/-- If two central elements `a, b` of `M(F)` have different norms under some rational
character, then a map `d` into `σ` with `σ(b) ∘ d = σ(a) ∘ d` is zero, for `σ` with no nonzero
vector fixed by an element none of whose positive powers lies in `⁰M(F)`. -/
theorem eq_zero_of_comp_centerEndomorphism_eq
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    {a b : rationalPoints M} (ha : a ∈ Subgroup.center (rationalPoints M))
    (hb : b ∈ Subgroup.center (rationalPoints M)) (χ : rationalCharacters M)
    (hχ : (Plancherel.rationalNormCharacters M χ).toMul b ≠
      (Plancherel.rationalNormCharacters M χ).toMul a)
    {Z : Rep.{max u v} ℂ (rationalPoints M)}
    (d : letI := leviPointTopology l hl; Z ⟶ SmoothRep.toRep.obj σ)
    (hd : letI := leviPointTopology l hl
      d ≫ SmoothRep.toRep.map (centerEndomorphism σ b hb) =
        d ≫ SmoothRep.toRep.map (centerEndomorphism σ a ha)) :
    d = 0 := by
  let := leviPointTopology l hl
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  change d.hom y = 0
  let Nχ := (Plancherel.rationalNormCharacters M χ).toMul
  let t := b⁻¹ * a
  have ht : ∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M := by
    intro n hn hmem
    have h1 : Nχ (t ^ n) = 1 := (Plancherel.mem_rationalCommonNormKernel M _).mp hmem χ
    have hx : (Nχ b)⁻¹ * Nχ a ≠ 1 := by
      rw [Ne, inv_mul_eq_one]
      exact hχ
    apply hx
    rw [map_pow, map_mul, map_inv] at h1
    apply Units.ext
    have h2 := congrArg (fun u : NNReal ˣ => (u : NNReal)) h1
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
    rw [Units.val_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp h2
  apply hfix t ht
  have h1 := congrArg (fun f => f.hom y) hd
  change σ.representation b (d.hom y) = σ.representation a (d.hom y) at h1
  change σ.representation (b⁻¹ * a) (d.hom y) = d.hom y
  rw [map_mul, Module.End.mul_apply, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Distinct orbits of an ordering of `P(F) \ G(F) / P(F)` have representatives `w_j, w_k` with
`w_j w_k⁻¹ ∉ M(F)`. -/
theorem not_mem_pointImage_of_ne {n : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage p) n) {j k : Fin n}
    (hjk : j ≠ k) :
    ((s.representative j)⁻¹)⁻¹ * (s.representative k)⁻¹ ∉ pointImage (l ≫ p) := by
  intro hmem
  have hP := pointImage_comp_le p l hmem
  rw [inv_inv] at hP
  have hxj : Induction.quotientMap (pointImage p) ((s.representative j)⁻¹ * 1) ∈
      Geometric.cosetOrbit (pointImage p) (pointImage p) (s.representative j) := ⟨1, rfl⟩
  have hxk : Induction.quotientMap (pointImage p) ((s.representative j)⁻¹ * 1) ∈
      Geometric.cosetOrbit (pointImage p) (pointImage p) (s.representative k) := by
    refine ⟨⟨(s.representative j * (s.representative k)⁻¹)⁻¹, (pointImage p).inv_mem hP⟩, ?_⟩
    change Induction.quotientMap (pointImage p)
        ((s.representative k)⁻¹ * (s.representative j * (s.representative k)⁻¹)⁻¹) =
      Induction.quotientMap (pointImage p) ((s.representative j)⁻¹ * 1)
    congr 1
    group
  exact Set.disjoint_left.mp (s.disjoint hjk) hxj hxk

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
set_option maxHeartbeats 800000 in
/-- For two full pieces of the geometric lemma for `r_P ∘ i_P` at `z_j, z_k` with
`z_j⁻¹ z_k ∉ M(F)`, some central `c` of `M(F)` and rational character `χ` separate the two
recovered point equivalences: `|χ|(ψ_j c) ≠ |χ|(ψ_k c)`. -/
theorem exists_center_norm_ne_of_fullPieces (hG : IsConnectedReductive G)
    {zj zk : rationalPoints G}
    (Dj : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul zj)
    (Dk : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul zk)
    [IsIso Dj.p'] [IsIso Dj.q'] [IsIso Dk.p'] [IsIso Dk.q']
    (hw : zj⁻¹ * zk ∉ pointImage (l ≫ p)) :
    ∃ c ∈ Subgroup.center (rationalPoints M), ∃ χ : rationalCharacters M,
      (Plancherel.rationalNormCharacters M χ).toMul (Dj.fullLeviPointsEquiv c) ≠
        (Plancherel.rationalNormCharacters M χ).toMul (Dk.fullLeviPointsEquiv c) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have hj : Dj.fullLeviConjugacy.val.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso zj⁻¹).hom :=
    Dj.fullLeviConjugacy.property
  have hk : Dk.fullLeviConjugacy.val.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso zk⁻¹).hom :=
    Dk.fullLeviConjugacy.property
  have hk' : Dk.fullLeviConjugacy.val.inv ≫ l ≫ p = l ≫ p ≫ (G.innerIso zk).hom := by
    rw [Iso.inv_comp_eq, reassoc_of% hk, ← G.innerIso_mul_hom, mul_inv_cancel,
      G.innerIso_one_hom, Category.comp_id]
  let φ : M ≅ M := Dk.fullLeviConjugacy.val.symm ≪≫ Dj.fullLeviConjugacy.val
  have hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (zj⁻¹ * zk)).hom := by
    change (Dk.fullLeviConjugacy.val.inv ≫ Dj.fullLeviConjugacy.val.hom) ≫ l ≫ p = _
    rw [Category.assoc, hj, reassoc_of% hk', G.innerIso_mul_hom]
  obtain ⟨a, ha, χ, hχ⟩ : ∃ a ∈ Subgroup.center (rationalPoints M),
      ∃ χ : rationalCharacters M,
        (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom a) ≠
          (Plancherel.rationalNormCharacters M χ).toMul a := by
    by_contra hne
    push Not at hne
    exact hw (leviNormalizerNormFixing k G hG P M p l hp hl (zj⁻¹ * zk) φ hφ hne)
  have hkc : Dk.fullLeviPointsEquiv (rationalPoints.map Dk.fullLeviConjugacy.val.inv a) = a := by
    rw [Dk.fullLeviPointsEquiv_apply, ← pointMap_comp_apply, Iso.inv_hom_id]
    rfl
  have hjc : Dj.fullLeviPointsEquiv (rationalPoints.map Dk.fullLeviConjugacy.val.inv a) =
      rationalPoints.map φ.hom a := by
    rw [Dj.fullLeviPointsEquiv_apply, ← pointMap_comp_apply]
    rfl
  refine ⟨rationalPoints.map Dk.fullLeviConjugacy.val.inv a, ?_, χ, ?_⟩
  · apply (mulEquiv_apply_mem_center_iff Dk.fullLeviPointsEquiv _).mp
    rw [hkc]
    exact ha
  · rw [hjc, hkc]
    exact hχ

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
set_option maxHeartbeats 1600000 in
/-- On every graded piece of the support filtration of `r_P(i_P σ)`, every map to `σ`
intertwines `ζ`, provided `ζ` commutes with all twisted-equivariant linear maps `σ → σ` and `σ`
is supercuspidal. -/
theorem leviJacquetSupportFiltration_graded_comm {n : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage p) n)
    (E : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      p l r hp hr hl hmul (s.representative i)⁻¹)
    (hF : (leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
      p l r hp hr hl hmul s).HasGradedPieces (fun i => (E i).pieceFunctor))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (ζ : letI := leviPointTopology l hl; σ ⟶ σ)
    (hζ : letI := leviPointTopology l hl
      ∀ (w : rationalPoints G) (φ : M ≅ M), φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
        ∀ T : σ →ₗ[ℂ] σ, (∀ (m : rationalPoints M) (v : σ),
          T (σ.representation m v) = σ.representation (rationalPoints.map φ.hom m) (T v)) →
        ∀ v : σ, T (SmoothRep.hom ζ v) = SmoothRep.hom ζ (T v))
    (i : Fin n)
    (g : letI := leviPointTopology l hl
      ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
        p l r hp hr hl hmul s).graded i).obj σ ⟶ SmoothRep.toRep.obj σ) :
    letI := leviPointTopology l hl
    ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
        p l r hp hr hl hmul s).graded i).map ζ ≫ g = g ≫ SmoothRep.toRep.map ζ := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let α := (hF i).some
  by_cases hpi : IsIso (E i).p'
  · have := (E i).isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
    refine map_comp_eq_comp_of_iso α ζ _ (fun g' => ?_) g
    exact fullPiece_hom_comm_of_twisted.{u, v} (E i) σ ζ
      (hζ _ _ (E i).fullLeviConjugacy.property) g'
  · have hsub : Subsingleton ((E i).pieceFunctor.obj σ) :=
      (E i).subsingleton_pieceFunctor_obj σ
        (hsc _ _ _ (E i).p' (E i).l' (E i).r' (E i).hp' (E i).hl' (E i).hr' (E i).hmul' hpi)
    have hg0 : g = 0 := eq_zero_of_iso_subsingleton α hsub g
    rw [hg0, Limits.comp_zero, Limits.zero_comp]

set_option maxHeartbeats 800000 in
/-- Two full pieces of the geometric lemma for `r_P ∘ i_P` at `z_j, z_k` with `z_j⁻¹ z_k ∉ M(F)`
are separated by central elements of `M(F)`. Let `A_j ≅` piece `j` and `A_k ≅` piece `k`. A map
`d : A_k σ → σ` vanishes as soon as it intertwines every pair `(a, β)` of endomorphisms commuting
with `ζ` that all maps `A_j σ → σ` intertwine. -/
theorem fullPieces_separated (hG : IsConnectedReductive G) {zj zk : rationalPoints G}
    (Dj : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul zj)
    (Dk : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul zk)
    [IsIso Dj.p'] [IsIso Dj.q'] [IsIso Dk.p'] [IsIso Dk.q']
    (hw : zj⁻¹ * zk ∉ pointImage (l ≫ p))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    (ζ : letI := leviPointTopology l hl; σ ⟶ σ)
    (hζc : letI := leviPointTopology l hl; ζ ∈ Subring.center (End σ))
    {Aj Ak : letI := leviPointTopology l hl
      SmoothRep.{0, u, max u v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints M)}
    (αj : letI := leviPointTopology l hl; Aj ≅ Dj.pieceFunctor)
    (αk : letI := leviPointTopology l hl; Ak ≅ Dk.pieceFunctor)
    (d : letI := leviPointTopology l hl; Ak.obj σ ⟶ SmoothRep.toRep.obj σ)
    (hd : letI := leviPointTopology l hl
      ∀ (a : σ ⟶ σ) (β : SmoothRep.toRep.obj σ ⟶ SmoothRep.toRep.obj σ), a ≫ ζ = ζ ≫ a →
        β ≫ SmoothRep.toRep.map ζ = SmoothRep.toRep.map ζ ≫ β →
        (∀ g : Aj.obj σ ⟶ SmoothRep.toRep.obj σ, Aj.map a ≫ g = g ≫ β) →
        Ak.map a ≫ d = d ≫ β) :
    d = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have hζcomm (x : End σ) : x ≫ ζ = ζ ≫ x :=
    ((Subring.mem_center_iff (R := End σ)).mp hζc x).symm
  obtain ⟨c', hc', χ, hχ⟩ := exists_center_norm_ne_of_fullPieces hG Dj Dk hw
  have hψj : Dj.fullLeviPointsEquiv c' ∈ Subgroup.center (rationalPoints M) :=
    (mulEquiv_apply_mem_center_iff Dj.fullLeviPointsEquiv c').mpr hc'
  have hψk : Dk.fullLeviPointsEquiv c' ∈ Subgroup.center (rationalPoints M) :=
    (mulEquiv_apply_mem_center_iff Dk.fullLeviPointsEquiv c').mpr hc'
  let aE := centerEndomorphism σ c' hc'
  let bE := centerEndomorphism σ (Dj.fullLeviPointsEquiv c') hψj
  let cE := centerEndomorphism σ (Dk.fullLeviPointsEquiv c') hψk
  have hβ : SmoothRep.toRep.map bE ≫ SmoothRep.toRep.map ζ =
      SmoothRep.toRep.map ζ ≫ SmoothRep.toRep.map bE := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hζcomm bE]
  have hj : ∀ g : Aj.obj σ ⟶ SmoothRep.toRep.obj σ,
      Aj.map aE ≫ g = g ≫ SmoothRep.toRep.map bE :=
    map_comp_eq_comp_of_iso αj aE _ (fullPiece_hom_comm_center.{u, v} Dj σ c' hc' hψj)
  have h1 : Ak.map aE ≫ d = d ≫ SmoothRep.toRep.map bE := hd aE _ (hζcomm aE) hβ hj
  have h2 : Ak.map aE ≫ d = d ≫ SmoothRep.toRep.map cE :=
    map_comp_eq_comp_of_iso αk aE _ (fullPiece_hom_comm_center.{u, v} Dk σ c' hc' hψk) d
  have h3 : d ≫ SmoothRep.toRep.map bE = d ≫ SmoothRep.toRep.map cE := h1.symm.trans h2
  exact eq_zero_of_comp_centerEndomorphism_eq.{u, v} σ hfix hψk hψj χ hχ d h3

set_option maxHeartbeats 1600000 in
/-- Distinct graded pieces of the support filtration of `r_P(i_P σ)` are separated by central
elements of `M(F)`: for `j < k`, a map `d` from the `k`-th piece to `σ` vanishes as soon as it
intertwines every pair `(a, β)` of endomorphisms commuting with `ζ` that all maps from the
`j`-th piece intertwine. -/
theorem leviJacquetSupportFiltration_graded_separated (hG : IsConnectedReductive G) {n : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage p) n)
    (E : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      p l r hp hr hl hmul (s.representative i)⁻¹)
    (hF : (leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
      p l r hp hr hl hmul s).HasGradedPieces (fun i => (E i).pieceFunctor))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    (ζ : letI := leviPointTopology l hl; σ ⟶ σ)
    (hζc : letI := leviPointTopology l hl; ζ ∈ Subring.center (End σ))
    (j k : Fin n) (hjk : j < k)
    (d : letI := leviPointTopology l hl
      ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
        p l r hp hr hl hmul s).graded k).obj σ ⟶ SmoothRep.toRep.obj σ)
    (hd : letI := leviPointTopology l hl
      ∀ (a : σ ⟶ σ) (β : SmoothRep.toRep.obj σ ⟶ SmoothRep.toRep.obj σ), a ≫ ζ = ζ ≫ a →
        β ≫ SmoothRep.toRep.map ζ = SmoothRep.toRep.map ζ ≫ β →
        (∀ g : ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
            p l r hp hr hl hmul s).graded j).obj σ ⟶ SmoothRep.toRep.obj σ,
          ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
            p l r hp hr hl hmul s).graded j).map a ≫ g = g ≫ β) →
        ((leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul
            p l r hp hr hl hmul s).graded k).map a ≫ d = d ≫ β) :
    d = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  let αj : _ ≅ (E j).pieceFunctor := (hF j).some
  let αk : _ ≅ (E k).pieceFunctor := (hF k).some
  by_cases hpk : IsIso (E k).p'
  swap
  · have hsub : Subsingleton ((E k).pieceFunctor.obj σ) :=
      (E k).subsingleton_pieceFunctor_obj σ
        (hsc _ _ _ (E k).p' (E k).l' (E k).r' (E k).hp' (E k).hl' (E k).hr' (E k).hmul' hpk)
    exact eq_zero_of_iso_subsingleton αk hsub d
  by_cases hpj : IsIso (E j).p'
  swap
  · have hsub : Subsingleton ((E j).pieceFunctor.obj σ) :=
      (E j).subsingleton_pieceFunctor_obj σ
        (hsc _ _ _ (E j).p' (E j).l' (E j).r' (E j).hp' (E j).hl' (E j).hr' (E j).hmul' hpj)
    have h1 := hd (𝟙 σ) 0 (by rw [Category.id_comp, Category.comp_id])
      (by rw [Limits.zero_comp, Limits.comp_zero]) (fun g => by
        rw [eq_zero_of_iso_subsingleton αj hsub g, Limits.comp_zero, Limits.zero_comp])
    rwa [CategoryTheory.Functor.map_id, Category.id_comp, Limits.comp_zero] at h1
  have := (E k).isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  have := (E j).isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  exact fullPieces_separated.{u, v} hG (E j) (E k) (not_mem_pointImage_of_ne s (ne_of_lt hjk))
    σ hfix ζ hζc αj αk d hd

set_option maxHeartbeats 1600000 in
/-- Let `σ` be a supercuspidal representation of `M(F)` in which no element `t` with
`t ^ n ∉ ⁰M(F)` for all `n > 0` fixes a nonzero vector, and `ζ` central in `End(σ)`. Suppose
that for every `w ∈ G(F)` and automorphism `φ` of `M` with `φ ≫ (M → G) = (M → G) ≫ Int(w)`,
`ζ` commutes with every linear `T : σ → σ` satisfying `T ∘ σ(m) = σ(φ m) ∘ T`. Then `i_P(ζ)` is
central in `End(i_P σ)`. -/
theorem leviInduction_map_mem_center_of_twistedCommutation (hG : IsConnectedReductive G)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    (ζ : letI := leviPointTopology l hl; σ ⟶ σ)
    (hζc : letI := leviPointTopology l hl; ζ ∈ Subring.center (End σ))
    (hζ : letI := leviPointTopology l hl
      ∀ (w : rationalPoints G) (φ : M ≅ M), φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom →
        ∀ T : σ →ₗ[ℂ] σ, (∀ (m : rationalPoints M) (v : σ),
          T (σ.representation m v) = σ.representation (rationalPoints.map φ.hom m) (T v)) →
        ∀ v : σ, T (SmoothRep.hom ζ v) = SmoothRep.hom ζ (T v)) :
    letI := leviPointTopology l hl
    (leviInductionFunctor p l r hp hr hl hmul).map ζ ∈
      Subring.center (End ((leviInductionFunctor p l r hp hr hl hmul).obj σ)) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  -- The double cosets `P(F) \ G(F) / P(F)` with their intersection data.
  obtain ⟨m, c, z, hz, ⟨D⟩⟩ :=
    representedGeometricLemmaGeometry k G hG P M N P M N p l r hp hl hr hmul
      p l r hp hl hr hmul
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space k G
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hPclosed := isClosed_pointImage p hp.isClosedSubgroup
  have hfinite : Finite (DoubleCoset.Quotient
      (pointImage p : Set (rationalPoints G)) (pointImage p : Set (rationalPoints G))) :=
    Finite.of_surjective c c.surjective
  obtain ⟨n, ⟨s⟩⟩ :=
    (Geometric.closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (rationalPoints G) (pointImage p) (pointImage p)
        hPclosed hPclosed hfinite
  have hbij : Function.Bijective
      (fun i : Fin m => DoubleCoset.mk (pointImage p) (pointImage p) ((z i)⁻¹)⁻¹) := by
    simpa only [inv_inv, hz] using c.bijective
  obtain ⟨e, t0, ht0⟩ := s.classifiedRepresentatives (fun i : Fin m => (z i)⁻¹) hbij
  have hrep (i : Fin n) : t0.representative i = (z (e i))⁻¹ := ht0 i
  let E : ∀ i : Fin n, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      p l r hp hr hl hmul (t0.representative i)⁻¹ := fun i => by
    rw [hrep i, inv_inv]
    exact D (e i)
  have hF := representedGeometricLemmaSupportGraded_of_orbitComparison.{u, max u v}
      arbitraryParabolicQuotientCompact parabolicRootPresentationExistence
      representedGeometricLemmaOrbitComparison
      k G hG P M N P M N p l r hp hl hr hmul p l r hp hl hr hmul n t0 E
  clear_value E
  have hA := leviJacquetSupportFiltration_graded_comm.{u, v} t0 E hF σ hsc ζ hζ
  have hB := leviJacquetSupportFiltration_graded_separated.{u, v} hG t0 E hF σ hsc hfix ζ hζc
  -- Frobenius reciprocity: every map `r_P(i_P σ) → σ` intertwines `ζ`.
  let I := leviInductionFunctor p l r hp hr hl hmul
  let J := leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul
  have key : ∀ (H : (J.obj (I.obj σ)).representation.IntertwiningMap σ.representation)
      (y : J.obj (I.obj σ)), H (SmoothRep.hom (J.map (I.map ζ)) y) = SmoothRep.hom ζ (H y) := by
    intro H y
    have h := RepFunctorFiltration.map_comp_eq_comp_of_graded
      (leviJacquetSupportFiltration.{u, max u v} p l r hp hr hl hmul p l r hp hr hl hmul t0)
      ζ (SmoothRep.toRep.map ζ)
      hA hB (Rep.ofHom H)
    exact congrArg (fun f => f.hom y) h
  obtain ⟨eF, heF⟩ := leviFrobeniusReciprocity k G hG P M N p l r hp hl hr hmul (I.obj σ) σ
  let mk := Jacquet.Localization.mk (I.obj σ).representation (pointImage (r ≫ p)) 1
  have hmk : Function.Surjective mk := Jacquet.Localization.mk_surjective _ _ _
  refine (Subring.mem_center_iff (R := End (I.obj σ))).mpr fun a => ?_
  have hx : SmoothRep.hom (I.map ζ ≫ a) = SmoothRep.hom (a ≫ I.map ζ) := by
    apply eF.injective
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
    obtain ⟨f, rfl⟩ := hmk w
    change eF (SmoothRep.hom (I.map ζ ≫ a)) (mk f) = eF (SmoothRep.hom (a ≫ I.map ζ)) (mk f)
    rw [heF, heF]
    have h1 := key (eF (SmoothRep.hom a)) (mk f)
    have h2 := heF (SmoothRep.hom a) (SmoothRep.hom (I.map ζ) f)
    have h3 := heF (SmoothRep.hom a) f
    change eF (SmoothRep.hom a) (mk (SmoothRep.hom (I.map ζ) f)) = _ at h1
    rw [h2, h3] at h1
    exact h1
  exact congrArg SmoothRep.ofHom hx

end Langlands.Aubert.General.RepresentedParabolic
