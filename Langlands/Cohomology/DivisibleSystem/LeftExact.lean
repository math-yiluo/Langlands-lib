import Langlands.Cohomology.DivisibleSystem.Coaugmented
import Langlands.Cohomology.SmoothSheafCohomology

/-!
# Left exact functors and `ℓ`-divisible systems

Harris 1999, §2, p.305: after truncating the resolution of Lemma 2.2, Harris checks that
the projections `j` of the top truncated term are surjective on sections over every étale
`U ⟶ U(ẽ)_F̄`. This module shows that the image of an `ℓ`-divisible system under an
additive functor preserving finite limits is again an `ℓ`-divisible system as soon as the
images of the projections `j` are epimorphisms; that is the only additional hypothesis.
Left exactness alone keeps the rows (2.1) exact except at their last term, and it keeps
the torsion condition and the defining equations. Flatness does not survive left
exactness alone: for `ℓ ≥ 2`, `F = Hom(ℤ/ℓ, -)` on abelian groups and `T m = ℤ/ℓ^m`, the
image of `T 2` is `ℤ/ℓ`, on which `ℓ` is zero. `map_flat` derives flatness using the
epimorphism hypothesis.
That hypothesis stays explicit: it is neither derived from acyclicity nor from a
cohomological-dimension bound here.

It also shows that the residual system `R q` of the coaugmented construction is, at every
level, the kernel of the differential `F^q ⟶ F^(q + 1)`, so it is the top term of the
truncation of the resolution, and it specializes the image construction to compact
sections and invariant compact sections of smooth sheaves.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

/-- An additive functor preserving finite limits preserves exactness of `X₁ ⟶ X₂ ⟶ X₃`
when `X₁ ⟶ X₂` is a monomorphism, and keeps `X₁ ⟶ X₂` a monomorphism. -/
lemma shortComplex_map_exact_of_mono {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (S : ShortComplex C) (hS : S.Exact) [Mono S.f] :
    (S.map F).Exact ∧ Mono (F.map S.f) := by
  have key : ∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae F).out 4 2).1 ‹PreservesFiniteLimits F›
  exact key S ⟨hS, inferInstance⟩

namespace DivisibleSystem

section Factorization

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

/-- For `0 < a` and `0 < b`, multiplication by `ℓ ^ a` on `T (a + b)` is the projection
`j : T (a + b) ⟶ T (a + b - a)`, followed by an isomorphism `T (a + b - a) ⟶ T b` and the
inclusion `i : T b ⟶ T (a + b)`. -/
lemma exists_powSMul_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ u : T.obj (a + b - a) ⟶ T.obj b, IsIso u ∧
      powSMul ℓ a (T.obj (a + b)) =
        T.projection (Nat.sub_le (a + b) a) ≫ u ≫ T.inclusion (by omega : b < a + b) := by
  have hlt : a < a + b := by omega
  have hb' : b < a + b := by omega
  have := T.epi_projection (Nat.sub_le (a + b) a)
  have w : T.inclusion hlt ≫ powSMul ℓ a (T.obj (a + b)) = 0 := by
    rw [comp_powSMul, T.powSMul_eq_zero, zero_comp]
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' (T.projectionIsCokernel hlt) _ w
  have hg' : T.projection (Nat.sub_le (a + b) a) ≫ g = powSMul ℓ a (T.obj (a + b)) := hg
  have hg0 : g ≫ powSMul ℓ b (T.obj (a + b)) = 0 := by
    rw [← cancel_epi (T.projection (Nat.sub_le (a + b) a)), reassoc_of% hg',
      powSMul_comp_powSMul, T.powSMul_eq_zero, comp_zero]
  obtain ⟨u, hu⟩ := KernelFork.IsLimit.lift' (T.inclusionIsKernel hb') g hg0
  have hu' : u ≫ T.inclusion hb' = g := hu
  have : Mono g := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A z hz
    obtain ⟨A₁, π₁, _, z₁, hz₁⟩ :=
      surjective_up_to_refinements_of_epi (T.projection (Nat.sub_le (a + b) a)) z
    have h₁ : z₁ ≫ powSMul ℓ a (T.obj (a + b)) = 0 := by
      rw [← hg', ← reassoc_of% hz₁, hz, comp_zero]
    obtain ⟨A₂, π₂, _, (s : A₂ ⟶ T.obj a), (hs : π₂ ≫ z₁ = s ≫ T.inclusion hlt)⟩ :=
      (T.torsion_exact hlt).exact_up_to_refinements z₁ h₁
    rw [← cancel_epi (π₂ ≫ π₁), comp_zero, Category.assoc, hz₁, reassoc_of% hs,
      T.inclusion_comp, comp_zero]
  have : Mono u := mono_of_mono_fac hu'
  have : Epi u := by
    rw [epi_iff_surjective_up_to_refinements]
    rintro A (y : A ⟶ T.obj b)
    have h₁ : (y ≫ T.inclusion hb') ≫ powSMul ℓ b (T.obj (a + b)) = 0 := by
      rw [Category.assoc, comp_powSMul, T.powSMul_eq_zero, zero_comp, comp_zero]
    obtain ⟨A₁, π₁, _, (t : A₁ ⟶ T.obj (a + b)),
      (ht : π₁ ≫ y ≫ T.inclusion hb' = t ≫ powSMul ℓ a (T.obj (a + b)))⟩ :=
      (T.flat a b).exact_up_to_refinements _ h₁
    refine ⟨A₁, π₁, inferInstance, t ≫ T.projection (Nat.sub_le (a + b) a), ?_⟩
    rw [← cancel_mono (T.inclusion hb')]
    simp only [Category.assoc]
    rw [hu', hg']
    exact ht
  have := isIso_of_mono_of_epi u
  exact ⟨u, inferInstance, by rw [hu', hg']⟩

end Factorization

section LeftExact

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {ℓ : ℕ} (T : DivisibleSystem C ℓ) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The image of the torsion condition: `F(i) : F(T m') ⟶ F(T m)` is a kernel of
multiplication by `ℓ ^ m'` on `F(T m)`. -/
lemma map_torsion_exact {m' m : ℕ} (h : m' < m) :
    (ShortComplex.mk (F.map (T.inclusion h)) (powSMul ℓ m' (F.obj (T.obj m)))
      (by rw [← map_powSMul, ← F.map_comp, comp_powSMul, T.powSMul_eq_zero, zero_comp,
        F.map_zero])).Exact :=
  shortComplex_exact_congr rfl (map_powSMul F _ _ _)
    (shortComplex_map_exact_of_mono F _ (T.torsion_exact h)).1

variable (hF : ∀ {m' m : ℕ} (h : m' ≤ m), Epi (F.map (T.projection h)))

include hF in
/-- Flatness of the image, from the factorization `ℓ ^ a = j ≫ u ≫ i` of
`exists_powSMul_eq` and the hypothesis that `F(j)` is an epimorphism. -/
lemma map_flat (a b : ℕ) :
    (ShortComplex.mk (powSMul ℓ a (F.obj (T.obj (a + b))))
      (powSMul ℓ b (F.obj (T.obj (a + b))))
      (by rw [powSMul_comp_powSMul, ← map_powSMul, T.powSMul_eq_zero, F.map_zero])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  rintro A (x : A ⟶ F.obj (T.obj (a + b)))
    (hx : x ≫ powSMul ℓ b (F.obj (T.obj (a + b))) = 0)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨A, 𝟙 A, inferInstance, x, ?_⟩
    show 𝟙 A ≫ x = x ≫ powSMul ℓ 0 (F.obj (T.obj (0 + b)))
    rw [powSMul_zero, Category.id_comp, Category.comp_id]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine ⟨A, 𝟙 A, inferInstance, 0, ?_⟩
    rw [powSMul_zero, Category.comp_id] at hx
    rw [hx, comp_zero, zero_comp]
  obtain ⟨u, _, hu⟩ := T.exists_powSMul_eq ha hb
  have hb' : b < a + b := by omega
  obtain ⟨A₁, π₁, _, (y : A₁ ⟶ F.obj (T.obj b)),
    (hy : π₁ ≫ x = y ≫ F.map (T.inclusion hb'))⟩ :=
    (T.map_torsion_exact F hb').exact_up_to_refinements x hx
  have := hF (Nat.sub_le (a + b) a)
  obtain ⟨A₂, π₂, _, (z : A₂ ⟶ F.obj (T.obj (a + b))), hz⟩ :=
    surjective_up_to_refinements_of_epi (F.map (T.projection (Nat.sub_le (a + b) a)))
      (y ≫ F.map (inv u))
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z, ?_⟩
  show (π₂ ≫ π₁) ≫ x = z ≫ powSMul ℓ a (F.obj (T.obj (a + b)))
  rw [← map_powSMul, hu, F.map_comp, F.map_comp, ← reassoc_of% hz, ← F.map_comp_assoc,
    IsIso.inv_hom_id, F.map_id, Category.id_comp, Category.assoc, hy]

/-- The image of an `ℓ`-divisible system under an additive functor preserving finite limits,
given that the images of the projections `j` are epimorphisms. -/
@[simps tower]
def mapLeftExact : DivisibleSystem D ℓ where
  tower := T.tower ⋙ F
  inclusion h := F.map (T.inclusion h)
  powSMul_eq_zero m := by
    rw [Functor.comp_obj, ← map_powSMul, T.powSMul_eq_zero, F.map_zero]
  inclusion_comp h := by
    rw [Functor.comp_map, ← F.map_comp, T.inclusion_comp, F.map_zero]
  shortExact {m' m} h := by
    have := (T.shortExact h).mono_f
    obtain ⟨hex, hmono⟩ := shortComplex_map_exact_of_mono F _ (T.shortExact h).exact
    exact { exact := hex, mono_f := hmono, epi_g := hF (Nat.sub_le m m') }
  torsion_exact h := T.map_torsion_exact F h
  flat a b := T.map_flat F hF a b

@[simp]
lemma mapLeftExact_inclusion {m' m : ℕ} (h : m' < m) :
    (T.mapLeftExact F hF).inclusion h = F.map (T.inclusion h) :=
  rfl

/-- For an exact functor, `mapLeftExact` is `map`. -/
lemma mapLeftExact_eq_map [PreservesFiniteColimits F] : T.mapLeftExact F hF = T.map F :=
  rfl

omit [Abelian D] [F.Additive] [PreservesFiniteLimits F] in
/-- It suffices that the images of the successive projections `T (m + 1) ⟶ T m` are
epimorphisms (the form of Harris's check on p.305). -/
lemma epi_map_projection_of_succ (h : ∀ m : ℕ, Epi (F.map (T.projection (Nat.le_succ m))))
    {m' m : ℕ} (hm : m' ≤ m) : Epi (F.map (T.projection hm)) := by
  induction m with
  | zero =>
    obtain rfl : m' = 0 := by omega
    rw [show T.projection hm = 𝟙 _ from
      (congrArg T.tower.map (Subsingleton.elim _ _)).trans (T.tower.map_id _), F.map_id]
    infer_instance
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rw [show T.projection hm = 𝟙 _ from
        (congrArg T.tower.map (Subsingleton.elim _ _)).trans (T.tower.map_id _), F.map_id]
      infer_instance
    · have hle : m' ≤ m := by omega
      have hcomp : T.projection hm = T.projection (Nat.le_succ m) ≫ T.projection hle :=
        (congrArg T.tower.map (Subsingleton.elim _ _)).trans (T.tower.map_comp _ _)
      have := h m
      have := ih hle
      rw [hcomp, F.map_comp]
      infer_instance

/-- A morphism of `ℓ`-divisible systems induces a morphism of their images. -/
@[simps tower]
def mapLeftExactHom {T' : DivisibleSystem C ℓ} (f : T ⟶ T')
    (hF' : ∀ {m' m : ℕ} (h : m' ≤ m), Epi (F.map (T'.projection h))) :
    T.mapLeftExact F hF ⟶ T'.mapLeftExact F hF' :=
  ⟨Functor.whiskerRight f.tower F, fun h =>
    (F.map_comp _ _).symm.trans ((congrArg F.map (f.comm h)).trans (F.map_comp _ _))⟩

end LeftExact

section Coaugmented

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ)

/-- At every level, `R q ⟶ F^q` is a kernel of the differential `F^q ⟶ F^(q + 1)`: the
residual system `R q` is the top term of the truncation in degree `q` of the resolution. -/
def residualInclusionIsKernel (q m : ℕ) :
    IsLimit (KernelFork.ofι ((T.residualInclusion F η q).tower.app (op m))
      (T.residualInclusion_termDifferential_tower_app F η q (op m))) :=
  (T.residualInclusion_termDifferential_exact F η q m).fIsKernel

/-- An additive functor `Φ` preserving finite limits carries `R q ⟶ F^q` to a kernel of
`Φ(F^q) ⟶ Φ(F^(q + 1))`, at every level. -/
def mapResidualInclusionIsKernel {D : Type u'} [Category.{v'} D] [Abelian D] (Φ : C ⥤ D)
    [Φ.Additive] [PreservesFiniteLimits Φ] (q m : ℕ) :
    IsLimit (KernelFork.ofι (Φ.map ((T.residualInclusion F η q).tower.app (op m)))
      (by rw [← Φ.map_comp, residualInclusion_termDifferential_tower_app, Φ.map_zero]) :
      Fork (Φ.map ((T.termDifferential F η q).tower.app (op m))) 0) :=
  isLimitForkMapOfIsLimit' Φ _ (T.residualInclusionIsKernel F η q m)

end Coaugmented

section Smooth

open Langlands.Sheaf.Equivariant Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}

/-- Compact sections of an `ℓ`-divisible system of smooth sheaves, as an `ℓ`-divisible
system of smooth representations, given that compact sections of the projections `j` are
epimorphisms. -/
def compactSectionsSystem (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map (T.projection h))) :
    DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ :=
  T.mapLeftExact (smoothSheafCompactSections R G X) hT

/-- Invariant compact sections of an `ℓ`-divisible system of smooth sheaves, as an
`ℓ`-divisible system of modules, given that invariant compact sections of the projections
`j` are epimorphisms. -/
def invariantCompactSectionsSystem (T : SmoothSheafDivisibleSystem R G X ℓ)
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map (T.projection h))) :
    DivisibleSystem (ModuleCat.{u} R) ℓ :=
  T.mapLeftExact (SmoothSheafCohomology.invariantCompactSections R G X) hT

variable (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)

/-- Compact sections of the smooth Godement term system `F^q`, given that compact sections
of its projections are epimorphisms. -/
def smoothGodementTermCompactSectionsSystem (q : ℕ)
    (hq : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementTermSystem h T q).projection hm))) :
    DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ :=
  compactSectionsSystem (smoothGodementTermSystem h T q) hq

/-- Compact sections of the smooth Godement residual system `R q`, the top term of the
truncated resolution, given that compact sections of its projections are epimorphisms. -/
def smoothGodementResidualCompactSectionsSystem (q : ℕ)
    (hq : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementResidualSystem h T q).projection hm))) :
    DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ :=
  compactSectionsSystem (smoothGodementResidualSystem h T q) hq

/-- Compact sections of the differential `F^q ⟶ F^(q + 1)` of the smooth Godement term
systems. -/
def smoothGodementTermCompactSectionsDifferential (q : ℕ)
    (hq : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hq' : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementTermSystem h T (q + 1)).projection hm))) :
    smoothGodementTermCompactSectionsSystem h T q hq ⟶
      smoothGodementTermCompactSectionsSystem h T (q + 1) hq' :=
  mapLeftExactHom _ _ hq (smoothGodementTermDifferential h T q) hq'

end Smooth

end DivisibleSystem

end Langlands.Cohomology
