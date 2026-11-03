import Langlands.Geometry.Building.KPBuilding

/-!
# The positive-depth groups `U_{a,x,r+}` and `U_{a,Ω,0+}`

For apartment data `D : KPApartmentData i ω` this module defines:

* `D.filtrationPlus x a r`, the group `U_{a,x,r+} = ⋃_{s>r} U_{a,x,s}` of KP Definition 6.1.2
  (indexing of the filtration by `R~`, conventions of KP §1.6);
* `D.rootFixerPlus a Ω = U_a(k) ∩ ⋂_{x ∈ Ω} U_{a,x,0+}`, the positive-depth analogue of the
  group `U_{a,Ω,0}` of KP Definition 7.4.1(1). For a facet `F` of `A` it is KP's `U_{a,F,0+}`
  (KP 6.3.21 and Corollary 7.4.9).

We prove the membership laws, the comparison with the affine root groups `U_{ψ+}` of KP
Definition 6.3.1, the translation law of KP Lemma 6.1.6 for `U_{a,x,r+}`, and the conjugation
law under the actual normalizer points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-! ### The groups `U_{a,x,r+}` -/

/-- `U_{a,x,r+} = ⋃_{s>r} U_{a,x,s}` (KP Definition 6.1.2, last paragraph). The union is
directed, so it is the subgroup supremum. -/
def filtrationPlus (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  ⨆ s : Set.Ioi r, D.filtration x a s

variable {D}

/-- `U_{a,x,r+} = {u ∈ U_a(k) | x_a(u) > r}`. -/
theorem mem_filtrationPlus {x : D.Apartment} {a : characterLattice S} {r : ℝ}
    {u : rationalPoints G} :
    u ∈ D.filtrationPlus x a r ↔ u ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) < x.val a u := by
  have : Nonempty (Set.Ioi r) := ⟨⟨r + 1, Set.mem_Ioi.2 (lt_add_one r)⟩⟩
  rw [filtrationPlus, Subgroup.mem_iSup_of_directed]
  · constructor
    · rintro ⟨s, hs⟩
      rw [mem_filtration] at hs
      exact ⟨hs.1, lt_of_lt_of_le (WithTop.coe_lt_coe.2 s.2) hs.2⟩
    · rintro ⟨hu, hlt⟩
      induction h : x.val a u using WithTop.recTopCoe with
      | top =>
        refine ⟨⟨r + 1, Set.mem_Ioi.2 (lt_add_one r)⟩, mem_filtration.2 ⟨hu, ?_⟩⟩
        rw [h]
        exact le_top
      | coe t =>
        rw [h, WithTop.coe_lt_coe] at hlt
        refine ⟨⟨t, hlt⟩, mem_filtration.2 ⟨hu, ?_⟩⟩
        rw [h]
  · intro s s'
    refine ⟨⟨min s s', Set.mem_Ioi.2 (lt_min s.2 s'.2)⟩, ?_, ?_⟩
    · exact filtration_antitone x a (min_le_left _ _)
    · exact filtration_antitone x a (min_le_right _ _)

theorem filtrationPlus_le_rootGroupPoints (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    D.filtrationPlus x a r ≤ rootGroupPoints i a :=
  fun _ hu => (mem_filtrationPlus.1 hu).1

/-- `U_{a,x,r+} ⊆ U_{a,x,r}`. -/
theorem filtrationPlus_le_filtration (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    D.filtrationPlus x a r ≤ D.filtration x a r :=
  iSup_le fun s => filtration_antitone x a (le_of_lt s.2)

/-- `U_{a,x,s} ⊆ U_{a,x,r+}` for `r < s`. -/
theorem filtration_le_filtrationPlus (x : D.Apartment) (a : characterLattice S) {r s : ℝ}
    (h : r < s) : D.filtration x a s ≤ D.filtrationPlus x a r :=
  le_iSup (fun t : Set.Ioi r => D.filtration x a t) ⟨s, h⟩

theorem filtrationPlus_antitone (x : D.Apartment) (a : characterLattice S) :
    Antitone (D.filtrationPlus x a) := fun _ _ hrr' _ hu =>
  mem_filtrationPlus.2 ⟨(mem_filtrationPlus.1 hu).1,
    lt_of_le_of_lt (WithTop.coe_le_coe.2 hrr') (mem_filtrationPlus.1 hu).2⟩

/-- `U_{a,x,r+} = U_{ψ+}` for the affine functional `ψ` with derivative `a` and `ψ(x) = r`
(KP Definition 6.3.1). -/
theorem filtrationPlus_eq_affineRootGroupPlus (α : relativeRoots i) (x : D.Apartment) (r : ℝ) :
    D.filtrationPlus x α r = D.affineRootGroupPlus α (D.affineFunctional α x r) := by
  ext u
  rw [mem_filtrationPlus, mem_affineRootGroupPlus_iff (affineFunctional_linear α x r) x,
    affineFunctional_apply, vsub_self, map_zero, zero_add]

/-- `U_{a,x+v,r+} = U_{a,x,(r-a(v))+}` (KP Lemma 6.1.6). -/
theorem filtrationPlus_vadd (x : D.Apartment) (v : TranslationSpace i) (α : relativeRoots i)
    (r : ℝ) :
    D.filtrationPlus (v +ᵥ x) α r = D.filtrationPlus x α (r - rootForm i α v) := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    rw [filtration_vadd]
    exact filtration_le_filtrationPlus x α (sub_lt_sub_right s.2 _)
  · refine iSup_le fun t => ?_
    have ht : r - rootForm i α v < t := t.2
    have h := filtration_le_filtrationPlus (v +ᵥ x) (α : characterLattice S)
      (r := r) (s := t + rootForm i α v) (by linarith)
    rwa [filtration_vadd, add_sub_cancel_right] at h

/-- `n U_{a,x,r+} n⁻¹ ⊆ U_{n·a,nx,r+}` for `n ∈ N(k)` (KP 6.1.8 and Fact 6.3.3). -/
theorem conj_mem_filtrationPlus (n : normalizerPoints i) {x : D.Apartment}
    {a : characterLattice S} {r : ℝ} {u : rationalPoints G} (hu : u ∈ D.filtrationPlus x a r) :
    (n : rationalPoints G) * u * (n : rationalPoints G)⁻¹ ∈
      D.filtrationPlus (n • x) (weylAction i n a) r := by
  rw [mem_filtrationPlus] at hu ⊢
  refine ⟨conj_mem_rootGroupPoints n hu.1, ?_⟩
  have hu' : (n : rationalPoints G)⁻¹ * ((n : rationalPoints G) * u * (n : rationalPoints G)⁻¹) *
      (n : rationalPoints G) = u := by
    group
  rw [val_smul, RootFunctionFamily.smul_apply, weylAction_inv_apply_apply, hu']
  exact hu.2

/-! ### The groups `U_{a,Ω,0+}` -/

variable (D)

/-- `U_{a,Ω,0+} = ⋂_{x ∈ Ω} U_{a,x,0+}`, the positive-depth analogue of KP
Definition 7.4.1(1), intersected with `U_a(k)` so that it is `U_a(k)` for empty `Ω`. For a facet
`F` it is the group `U_{a,F,0+}` of KP 6.3.21 and Corollary 7.4.9. -/
def rootFixerPlus (a : characterLattice S) (Ω : Set D.Apartment) :
    Subgroup (rationalPoints G) :=
  rootGroupPoints i a ⊓ ⨅ x ∈ Ω, D.filtrationPlus x a 0

theorem mem_rootFixerPlus_iff_forall_mem {a : characterLattice S} {Ω : Set D.Apartment}
    {u : rationalPoints G} :
    u ∈ D.rootFixerPlus a Ω ↔ u ∈ rootGroupPoints i a ∧ ∀ x ∈ Ω, u ∈ D.filtrationPlus x a 0 := by
  simp only [rootFixerPlus, Subgroup.mem_inf, Subgroup.mem_iInf]

/-- `U_{a,Ω,0+} = {u ∈ U_a(k) | x_a(u) > 0 for all x ∈ Ω}`. -/
theorem mem_rootFixerPlus {a : characterLattice S} {Ω : Set D.Apartment}
    {u : rationalPoints G} :
    u ∈ D.rootFixerPlus a Ω ↔ u ∈ rootGroupPoints i a ∧ ∀ x ∈ Ω, 0 < x.val a u := by
  rw [mem_rootFixerPlus_iff_forall_mem]
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, fun x hx => by simpa using (mem_filtrationPlus.1 (h x hx)).2⟩
  · rintro ⟨hu, h⟩
    exact ⟨hu, fun x hx => mem_filtrationPlus.2 ⟨hu, by simpa using h x hx⟩⟩

theorem rootFixerPlus_empty (a : characterLattice S) :
    D.rootFixerPlus a ∅ = rootGroupPoints i a := by
  ext u
  simp [mem_rootFixerPlus]

/-- `U_{a,{x},0+} = U_{a,x,0+}`. -/
theorem rootFixerPlus_singleton (a : characterLattice S) (x : D.Apartment) :
    D.rootFixerPlus a {x} = D.filtrationPlus x a 0 := by
  ext u
  rw [mem_rootFixerPlus_iff_forall_mem, Set.forall_mem_singleton]
  exact ⟨fun h => h.2, fun h => ⟨filtrationPlus_le_rootGroupPoints x a 0 h, h⟩⟩

/-- `U_{a,{x},0+} = ⋃_{s>0} U_{a,x,s}`. -/
theorem rootFixerPlus_singleton_eq_iSup (a : characterLattice S) (x : D.Apartment) :
    D.rootFixerPlus a {x} = ⨆ s : Set.Ioi (0 : ℝ), D.filtration x a s :=
  D.rootFixerPlus_singleton a x

/-- `U_{a,{x},0+} = U_{ψ+}` for the affine functional `ψ` with derivative `a` vanishing at `x`. -/
theorem rootFixerPlus_singleton_eq_affineRootGroupPlus (α : relativeRoots i) (x : D.Apartment) :
    D.rootFixerPlus α {x} = D.affineRootGroupPlus α (D.affineFunctional α x 0) := by
  rw [rootFixerPlus_singleton, filtrationPlus_eq_affineRootGroupPlus]

/-- `U_{a,Ω,0+} ⊆ U_{a,Ω,0}`. -/
theorem rootFixerPlus_le_rootFixer (a : characterLattice S) (Ω : Set D.Apartment) :
    D.rootFixerPlus a Ω ≤ D.rootFixer a Ω := fun _ hu =>
  D.mem_rootFixer.2 ⟨((D.mem_rootFixerPlus_iff_forall_mem).1 hu).1, fun x hx =>
    filtrationPlus_le_filtration x a 0 (((D.mem_rootFixerPlus_iff_forall_mem).1 hu).2 x hx)⟩

theorem rootFixerPlus_anti (a : characterLattice S) {Ω Ω' : Set D.Apartment} (h : Ω ⊆ Ω') :
    D.rootFixerPlus a Ω' ≤ D.rootFixerPlus a Ω := fun _ hu =>
  (D.mem_rootFixerPlus_iff_forall_mem).2 ⟨((D.mem_rootFixerPlus_iff_forall_mem).1 hu).1,
    fun x hx => ((D.mem_rootFixerPlus_iff_forall_mem).1 hu).2 x (h hx)⟩

/-- `n U_{a,Ω,0+} n⁻¹ ⊆ U_{n·a,nΩ,0+}` for `n ∈ N(k)`. -/
theorem conj_mem_rootFixerPlus (n : normalizerPoints i) {a : characterLattice S}
    {Ω : Set D.Apartment} {u : rationalPoints G} (hu : u ∈ D.rootFixerPlus a Ω) :
    (n : rationalPoints G) * u * (n : rationalPoints G)⁻¹ ∈
      D.rootFixerPlus (weylAction i n a) (n • Ω) := by
  rw [mem_rootFixerPlus_iff_forall_mem] at hu ⊢
  refine ⟨conj_mem_rootGroupPoints n hu.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact conj_mem_filtrationPlus n (hu.2 x hx)

end KPApartmentData

end Langlands.Geometry.Building
