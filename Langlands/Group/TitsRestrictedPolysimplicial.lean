import Langlands.Group.TitsSystemExchange
import Langlands.Geometry.Building.AbstractBuilding

/-! # The restricted building of a Tits system is polysimplicial -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

/-! ### Irreducible components of `S` -/

namespace TitsSystem

variable {W : Type*} [Group W] {S : Set W}

theorem sameComponent_symm {s t : W} (hst : SameComponent S s t) : SameComponent S t s := by
  induction hst with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, fun e => hbc.2.2 e.symm⟩ ih

variable (S) in
/-- The equivalence relation on `S` whose classes are its irreducible components. -/
def componentSetoid : Setoid S where
  r s t := SameComponent S s t
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl, sameComponent_symm,
    Relation.ReflTransGen.trans⟩

variable (S) in
/-- The irreducible components `Sᵢ` of `S` (KP §1.4, after Definition 1.4.6). -/
def Component : Type _ :=
  Quotient (componentSetoid S)

/-- The component of an element of `S`. -/
def componentOf (s : S) : Component S :=
  Quotient.mk (componentSetoid S) s

/-- The elements of `S` lying in the component `c`. -/
def componentSet (c : Component S) : Set W :=
  {s | ∃ hs : s ∈ S, componentOf ⟨s, hs⟩ = c}

instance [Finite S] : Finite (Component S) :=
  Quotient.finite _

theorem componentSet_subset (c : Component S) : componentSet c ⊆ S :=
  fun _ hs => hs.1

theorem mem_componentSet_componentOf (s : S) : (s : W) ∈ componentSet (componentOf s) :=
  ⟨s.2, rfl⟩

theorem componentSet_nonempty (c : Component S) : (componentSet c).Nonempty := by
  induction c using Quotient.inductionOn with
  | h s => exact ⟨s, s.2, rfl⟩

theorem eq_of_mem_componentSet {c d : Component S} {s : W} (hc : s ∈ componentSet c)
    (hd : s ∈ componentSet d) : c = d := by
  obtain ⟨hs, rfl⟩ := hc
  obtain ⟨hs', rfl⟩ := hd
  rfl

theorem sameComponent_of_mem_componentSet {c : Component S} {s t : W}
    (hs : s ∈ componentSet c) (ht : t ∈ componentSet c) : SameComponent S s t := by
  obtain ⟨hsS, hsc⟩ := hs
  obtain ⟨htS, rfl⟩ := ht
  exact Quotient.exact (s := componentSetoid S) hsc

theorem mem_componentSet_of_sameComponent {c : Component S} {s t : W}
    (hs : s ∈ componentSet c) (htS : t ∈ S) (hst : SameComponent S s t) :
    t ∈ componentSet c := by
  obtain ⟨hsS, rfl⟩ := hs
  exact ⟨htS, (Quotient.sound (s := componentSetoid S) hst).symm⟩

/-- Elements of `S` in different components commute. -/
theorem commute_of_not_mem_componentSet {c : Component S} {s t : W}
    (hs : s ∈ componentSet c) (ht : t ∈ S) (htc : t ∉ componentSet c) : s * t = t * s := by
  by_contra hne
  exact htc (mem_componentSet_of_sameComponent hs ht
    (Relation.ReflTransGen.single ⟨hs.1, ht, hne⟩))

/-- Admissibility, component by component (KP Definition 1.5.17(1)). -/
theorem isAdmissibleType_iff {X : Set W} :
    IsAdmissibleType S X ↔ X ⊆ S ∧ ∀ c : Component S, ∃ t ∈ componentSet c, t ∉ X := by
  constructor
  · rintro ⟨hXS, hX⟩
    refine ⟨hXS, fun c => ?_⟩
    obtain ⟨s, hs⟩ := componentSet_nonempty c
    obtain ⟨t, htS, hst, htX⟩ := hX s hs.1
    exact ⟨t, mem_componentSet_of_sameComponent hs htS hst, htX⟩
  · rintro ⟨hXS, hX⟩
    refine ⟨hXS, fun s hs => ?_⟩
    obtain ⟨t, ht, htX⟩ := hX (componentOf ⟨s, hs⟩)
    exact ⟨t, ht.1, sameComponent_of_mem_componentSet
      (mem_componentSet_componentOf ⟨s, hs⟩) ht, htX⟩

/-- Commuting subsets of a group generate commuting subgroups. -/
theorem commute_of_mem_closure {A C : Set W} (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    {u v : W} (hu : u ∈ Subgroup.closure A) (hv : v ∈ Subgroup.closure C) :
    u * v = v * u := by
  have h₁ : Subgroup.closure C ≤ Subgroup.centralizer A :=
    (Subgroup.closure_le _).mpr fun c hc =>
      Subgroup.mem_centralizer_iff.mpr fun a ha => hAC a ha c hc
  have h₂ : Subgroup.closure A ≤ Subgroup.centralizer (Subgroup.closure C : Set W) :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun c hc =>
      ((Subgroup.mem_centralizer_iff.mp (h₁ hc)) a ha).symm
  exact ((Subgroup.mem_centralizer_iff.mp (h₂ hu)) v hv).symm

/-! ### Conjugate subgroups -/

section Conjugate

variable {G : Type*} [Group G]

theorem mem_conjugateSubgroup_iff_inv {g x : G} {L : Subgroup G} :
    x ∈ conjugateSubgroup g L ↔ g⁻¹ * x * g ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem conjugateSubgroup_inv_cancel (g : G) (L : Subgroup G) :
    conjugateSubgroup g⁻¹ (conjugateSubgroup g L) = L := by
  rw [← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one]

theorem conjugateSubgroup_mono (g : G) {L M : Subgroup G} (hLM : L ≤ M) :
    conjugateSubgroup g L ≤ conjugateSubgroup g M :=
  Subgroup.map_mono hLM

theorem conjugateSubgroup_le_conjugateSubgroup_iff (g : G) {L M : Subgroup G} :
    conjugateSubgroup g L ≤ conjugateSubgroup g M ↔ L ≤ M := by
  refine ⟨fun hLM => ?_, conjugateSubgroup_mono g⟩
  have := conjugateSubgroup_mono g⁻¹ hLM
  rwa [conjugateSubgroup_inv_cancel, conjugateSubgroup_inv_cancel] at this

end Conjugate

end TitsSystem

/-! ### Product decompositions in a Tits system -/

namespace IsTitsSystem

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}
  (h : IsTitsSystem B N π S)
include h

/-- If the elements of `T ⊆ S` commute with those of `S \ T`, then
`W = W_{S \ T} W_T`. -/
theorem exists_mul_eq_of_commute {T : Set W}
    (hcomm : ∀ t ∈ T, ∀ s ∈ S \ T, t * s = s * t) (w : W) :
    ∃ u ∈ Subgroup.closure (S \ T), ∃ v ∈ Subgroup.closure T, w = u * v := by
  have hc : ∀ u ∈ Subgroup.closure (S \ T), ∀ v ∈ Subgroup.closure T, v * u = u * v :=
    fun u hu v hv => commute_of_mem_closure (fun t ht s hs => hcomm t ht s hs) hv hu
  have hw : w ∈ Subgroup.closure S := h.closure_eq ▸ Subgroup.mem_top w
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    by_cases hsT : s ∈ T
    · exact ⟨1, Subgroup.one_mem _, s, Subgroup.subset_closure hsT, by simp⟩
    · exact ⟨s, Subgroup.subset_closure ⟨hs, hsT⟩, 1, Subgroup.one_mem _, by simp⟩
  | one => exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hy
    refine ⟨u * u', Subgroup.mul_mem _ hu hu', v * v', Subgroup.mul_mem _ hv hv', ?_⟩
    calc u * v * (u' * v') = u * ((v * u') * v') := by simp only [mul_assoc]
      _ = u * ((u' * v) * v') := by rw [hc u' hu' v hv]
      _ = u * u' * (v * v') := by simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    refine ⟨u⁻¹, Subgroup.inv_mem _ hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
    rw [mul_inv_rev]
    exact hc u⁻¹ (Subgroup.inv_mem _ hu) v⁻¹ (Subgroup.inv_mem _ hv)

/-- If the elements of `T ⊆ S` commute with those of `S \ T`, then
`G = G_{S \ T} G_T`. -/
theorem exists_mul_eq_standardParabolic {T : Set W} (hT : T ⊆ S)
    (hcomm : ∀ t ∈ T, ∀ s ∈ S \ T, t * s = s * t) (g : G) :
    ∃ y ∈ h.standardParabolicSubgroup (Set.sdiff_subset : S \ T ⊆ S),
      ∃ z ∈ h.standardParabolicSubgroup hT, g = y * z := by
  obtain ⟨w, hw⟩ := h.exists_mem_cell g
  obtain ⟨u, hu, v, hv, rfl⟩ := h.exists_mul_eq_of_commute hcomm w
  obtain ⟨nu, hnu⟩ := h.surjective u
  obtain ⟨nv, hnv⟩ := h.surjective v
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ :=
    h.exists_eq_of_mem_cell hw (n := nu * nv) (by simp [hnu, hnv])
  refine ⟨b₁ * nu, ⟨u, hu, mul_mem_cell_left (mem_cell_of_eq hnu) hb₁⟩,
    nv * b₂, ⟨v, hv, mul_mem_cell_right (mem_cell_of_eq hnv) hb₂⟩, ?_⟩
  simp [mul_assoc]

/-- Cosets of the complements of the components have a common point
(the surjectivity step of KP Proposition 1.4.10). -/
theorem exists_forall_inv_mul_mem [Finite S] (g : Component S → G) :
    ∃ x : G, ∀ c, (g c)⁻¹ * x ∈
      h.standardParabolicSubgroup (Set.sdiff_subset : S \ componentSet c ⊆ S) := by
  classical
  have : Fintype (Component S) := Fintype.ofFinite _
  suffices ∀ J : Finset (Component S), ∃ x : G, ∀ c ∈ J, (g c)⁻¹ * x ∈
      h.standardParabolicSubgroup (Set.sdiff_subset : S \ componentSet c ⊆ S) by
    obtain ⟨x, hx⟩ := this Finset.univ
    exact ⟨x, fun c => hx c (Finset.mem_univ c)⟩
  intro J
  induction J using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert m J hm ih =>
    obtain ⟨x, hx⟩ := ih
    let T : Set W := {s | ∃ c ∈ J, s ∈ componentSet c}
    have hT : T ⊆ S := fun s ⟨c, _, hs⟩ => componentSet_subset c hs
    have hcomm : ∀ t ∈ T, ∀ s ∈ S \ T, t * s = s * t := by
      rintro t ⟨c, hc, htc⟩ s ⟨hsS, hsT⟩
      exact commute_of_not_mem_componentSet htc hsS fun hsc => hsT ⟨c, hc, hsc⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := h.exists_mul_eq_standardParabolic hT hcomm (x⁻¹ * g m)
    have hy' : y = x⁻¹ * g m * z⁻¹ := eq_mul_inv_of_mul_eq hyz.symm
    have hm' : (g m)⁻¹ * (x * y) ∈
        h.standardParabolicSubgroup (Set.sdiff_subset : S \ componentSet m ⊆ S) := by
      have heq : (g m)⁻¹ * (x * y) = z⁻¹ := by rw [hy']; simp [mul_assoc]
      rw [heq]
      refine (h.standardParabolicSubgroup_le_iff hT Set.sdiff_subset).mpr ?_
        (Subgroup.inv_mem _ hz)
      rintro t ⟨d, hd, htd⟩
      refine ⟨componentSet_subset d htd, fun htc => ?_⟩
      exact hm (eq_of_mem_componentSet htd htc ▸ hd)
    refine ⟨x * y, fun c hc => ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hm'
    · have hle := (h.standardParabolicSubgroup_le_iff (Set.sdiff_subset : S \ T ⊆ S)
        (Set.sdiff_subset : S \ componentSet c ⊆ S)).mpr
        (Set.sdiff_subset_sdiff_right fun s hs => ⟨c, hc, hs⟩)
      rw [← mul_assoc]
      exact Subgroup.mul_mem _ (hx c hc) (hle hy)

/-! ### Vertices and simplices of the component buildings -/

/-- The parabolic subgroup `g G_{S \ {s}} g⁻¹`. -/
def maximalParabolic (g : G) (s : W) : Subgroup G :=
  conjugateSubgroup g (h.standardParabolicSubgroup (Set.sdiff_subset : S \ {s} ⊆ S))

/-- `Q` is a vertex of the building of the component `c`: a parabolic
subgroup of type `S \ {s}` with `s` in `c` (KP Lemma 1.4.9 and
Proposition 1.4.10, applied to `Sᵢ` and its complement). -/
def IsComponentVertex (c : Component S) (Q : Subgroup G) : Prop :=
  ∃ (g : G) (s : W), s ∈ componentSet c ∧ Q = h.maximalParabolic g s

/-- The vertices of the building of the component `c`. -/
def ComponentVertex (c : Component S) : Type _ :=
  {Q : Subgroup G // h.IsComponentVertex c Q}

/-- The simplex of the component building attached to a parabolic subgroup:
the vertices of that component containing it. -/
def componentFace (c : Component S) (P : Subgroup G) : Set (h.ComponentVertex c) :=
  {Q | P ≤ Q.1}

theorem mem_componentFace {c : Component S} {P : Subgroup G} {Q : h.ComponentVertex c} :
    Q ∈ h.componentFace c P ↔ P ≤ Q.1 :=
  Iff.rfl

/-- An admissible parabolic subgroup is a conjugate of a standard parabolic
subgroup of admissible type. -/
theorem exists_eq_conjugate_of_isAdmissibleParabolic {P : Subgroup G}
    (hP : IsAdmissibleParabolic B π S P) :
    ∃ (g : G) (X : Set W) (hX : IsAdmissibleType S X),
      P = conjugateSubgroup g (h.standardParabolicSubgroup hX.1) := by
  obtain ⟨g, X, hX, hP⟩ := hP
  exact ⟨g, X, hX, SetLike.coe_injective (hP.trans
    (h.coe_conjugate_standardParabolic hX.1 g).symm)⟩

theorem isAdmissibleParabolic_conjugate_standard {X : Set W} (hX : IsAdmissibleType S X)
    (g : G) :
    IsAdmissibleParabolic B π S (conjugateSubgroup g (h.standardParabolicSubgroup hX.1)) :=
  ⟨g, X, hX, h.coe_conjugate_standardParabolic hX.1 g⟩

/-- The vertices of a component containing `g G_X g⁻¹` are the conjugates
`g G_{S \ {s}} g⁻¹` with `s` in the component and outside `X`. -/
theorem conjugate_le_iff_of_isComponentVertex {c : Component S} {X : Set W} (hX : X ⊆ S)
    (g : G) {Q : Subgroup G} (hQ : h.IsComponentVertex c Q) :
    conjugateSubgroup g (h.standardParabolicSubgroup hX) ≤ Q ↔
      ∃ s, s ∈ componentSet c ∧ s ∉ X ∧ Q = h.maximalParabolic g s := by
  constructor
  · intro hle
    obtain ⟨k, t, ht, rfl⟩ := hQ
    let P' := conjugateSubgroup (g⁻¹ * k)
      (h.standardParabolicSubgroup (Set.sdiff_subset : S \ {t} ⊆ S))
    have hle' : h.standardParabolicSubgroup hX ≤ P' := by
      have := conjugateSubgroup_mono g⁻¹ hle
      rwa [conjugateSubgroup_inv_cancel, maximalParabolic, ← conjugateSubgroup_mul] at this
    have hBP' : B ≤ P' := (h.le_of_coe_eq rfl).trans hle'
    have hmem : g⁻¹ * k ∈ P' := h.mem_of_eq_conjugate hBP' (h.le_of_coe_eq rfl) rfl
    have hP' : P' = h.standardParabolicSubgroup (Set.sdiff_subset : S \ {t} ⊆ S) := by
      calc P' = conjugateSubgroup (g⁻¹ * k)⁻¹ P' :=
            (conjugateSubgroup_eq_self (P'.inv_mem hmem)).symm
        _ = _ := conjugateSubgroup_inv_cancel _ _
    refine ⟨t, ht, ?_, ?_⟩
    · have hXt := (h.standardParabolicSubgroup_le_iff hX Set.sdiff_subset).mp (hP' ▸ hle')
      exact fun htX => (hXt htX).2 rfl
    · change conjugateSubgroup k _ = conjugateSubgroup g _
      calc conjugateSubgroup k (h.standardParabolicSubgroup (Set.sdiff_subset : S \ {t} ⊆ S))
          = conjugateSubgroup (g * (g⁻¹ * k))
              (h.standardParabolicSubgroup (Set.sdiff_subset : S \ {t} ⊆ S)) := by
            rw [mul_inv_cancel_left]
        _ = conjugateSubgroup g P' := conjugateSubgroup_mul _ _ _
        _ = _ := by rw [hP']
  · rintro ⟨s, -, hsX, rfl⟩
    exact conjugateSubgroup_mono g ((h.standardParabolicSubgroup_le_iff hX Set.sdiff_subset).mpr
      fun x hx => ⟨hX hx, fun hxs => hsX ((Set.mem_singleton_iff.mp hxs) ▸ hx)⟩)

/-- Different elements of `S` give different maximal parabolic subgroups. -/
theorem maximalParabolic_eq_iff {s t : W} (hs : s ∈ S) (g : G) :
    h.maximalParabolic g s = h.maximalParabolic g t ↔ s = t := by
  refine ⟨fun he => ?_, fun he => he ▸ rfl⟩
  have hST := h.eq_of_conjugateSubgroup_eq Set.sdiff_subset Set.sdiff_subset g g he
  by_contra hne
  have : s ∈ S \ {t} := ⟨hs, hne⟩
  rw [← hST] at this
  exact this.2 rfl

/-- Right multiplication by an element of `G_{S \ {s}}` does not change the
maximal parabolic subgroup. -/
theorem maximalParabolic_mul_of_mem {g k : G} {s : W}
    (hk : k ∈ h.standardParabolicSubgroup (Set.sdiff_subset : S \ {s} ⊆ S)) :
    h.maximalParabolic (g * k) s = h.maximalParabolic g s := by
  rw [maximalParabolic, conjugateSubgroup_mul, conjugateSubgroup_eq_self hk]
  rfl

variable [Finite S]

/-- The building of the component `c` as a simplicial complex: its simplices are
the sets of component vertices containing an admissible parabolic subgroup. -/
def componentComplex (c : Component S) :
    Langlands.Geometry.Building.AbstractBuilding.SimplicialComplex (h.ComponentVertex c) where
  faces := {σ | ∃ P, IsAdmissibleParabolic B π S P ∧ σ = h.componentFace c P}
  nonempty_vertices := by
    obtain ⟨s, hs⟩ := componentSet_nonempty c
    exact ⟨⟨h.maximalParabolic 1 s, 1, s, hs, rfl⟩⟩
  finite_of_mem := by
    rintro σ ⟨P, hP, rfl⟩
    obtain ⟨g, X, hX, rfl⟩ := h.exists_eq_conjugate_of_isAdmissibleParabolic hP
    have : Finite (componentSet c) :=
      ((Set.toFinite S).subset (componentSet_subset c)).to_subtype
    refine (Set.finite_range (fun s : componentSet c =>
      (⟨h.maximalParabolic g s, g, s, s.2, rfl⟩ : h.ComponentVertex c))).subset ?_
    intro Q hQ
    obtain ⟨s, hs, -, hQs⟩ := (h.conjugate_le_iff_of_isComponentVertex hX.1 g Q.2).mp hQ
    exact ⟨⟨s, hs⟩, Subtype.ext hQs.symm⟩
  nonempty_of_mem := by
    rintro σ ⟨P, hP, rfl⟩
    obtain ⟨g, X, hX, rfl⟩ := h.exists_eq_conjugate_of_isAdmissibleParabolic hP
    obtain ⟨t, ht, htX⟩ := (isAdmissibleType_iff.mp hX).2 c
    exact ⟨⟨h.maximalParabolic g t, g, t, ht, rfl⟩,
      (h.conjugate_le_iff_of_isComponentVertex hX.1 g ⟨g, t, ht, rfl⟩).mpr ⟨t, ht, htX, rfl⟩⟩
  singleton_mem := by
    intro Q
    obtain ⟨k, s, hs, hQ⟩ := Q.2
    have hX : IsAdmissibleType S (componentSet c \ {s}) := by
      refine isAdmissibleType_iff.mpr ⟨fun x hx => componentSet_subset c hx.1, fun d => ?_⟩
      by_cases hdc : d = c
      · subst hdc
        exact ⟨s, hs, fun h' => h'.2 rfl⟩
      · obtain ⟨t, ht⟩ := componentSet_nonempty d
        exact ⟨t, ht, fun h' => hdc (eq_of_mem_componentSet ht h'.1)⟩
    refine ⟨_, h.isAdmissibleParabolic_conjugate_standard hX k, ?_⟩
    ext Q'
    rw [Set.mem_singleton_iff, mem_componentFace,
      h.conjugate_le_iff_of_isComponentVertex hX.1 k Q'.2]
    constructor
    · rintro rfl
      exact ⟨s, hs, fun h' => h'.2 rfl, hQ⟩
    · rintro ⟨s', hs', hs'X, hQ's⟩
      have hss' : s' = s := by
        by_contra hne
        exact hs'X ⟨hs', hne⟩
      subst hss'
      exact Subtype.ext (hQ's.trans hQ.symm)
  mem_of_subset := by
    rintro σ ⟨P, hP, rfl⟩ τ hτne hτ
    obtain ⟨g, X, hX, rfl⟩ := h.exists_eq_conjugate_of_isAdmissibleParabolic hP
    let T : Set W := {s | s ∈ componentSet c ∧ ∃ Q ∈ τ, Q.1 = h.maximalParabolic g s}
    have hX' : IsAdmissibleType S ((X \ componentSet c) ∪ (componentSet c \ T)) := by
      refine isAdmissibleType_iff.mpr ⟨?_, fun d => ?_⟩
      · rintro x (⟨hx, -⟩ | ⟨hx, -⟩)
        · exact hX.1 hx
        · exact componentSet_subset c hx
      · by_cases hdc : d = c
        · subst hdc
          obtain ⟨Q, hQ⟩ := hτne
          obtain ⟨s, hs, -, hQs⟩ :=
            (h.conjugate_le_iff_of_isComponentVertex hX.1 g Q.2).mp (hτ hQ)
          refine ⟨s, hs, ?_⟩
          rintro (⟨-, hsc⟩ | ⟨-, hsT⟩)
          · exact hsc hs
          · exact hsT ⟨hs, Q, hQ, hQs⟩
        · obtain ⟨t, ht, htX⟩ := (isAdmissibleType_iff.mp hX).2 d
          refine ⟨t, ht, ?_⟩
          rintro (⟨htX', -⟩ | ⟨htc, -⟩)
          · exact htX htX'
          · exact hdc (eq_of_mem_componentSet ht htc)
    refine ⟨_, h.isAdmissibleParabolic_conjugate_standard hX' g, ?_⟩
    ext Q
    rw [mem_componentFace, h.conjugate_le_iff_of_isComponentVertex hX'.1 g Q.2]
    constructor
    · intro hQτ
      obtain ⟨s, hs, -, hQs⟩ :=
        (h.conjugate_le_iff_of_isComponentVertex hX.1 g Q.2).mp (hτ hQτ)
      refine ⟨s, hs, ?_, hQs⟩
      rintro (⟨-, hsc⟩ | ⟨-, hsT⟩)
      · exact hsc hs
      · exact hsT ⟨hs, Q, hQτ, hQs⟩
    · rintro ⟨s, hs, hsX', hQs⟩
      have hsT : s ∈ T := by
        by_contra hsT
        exact hsX' (Or.inr ⟨hs, hsT⟩)
      obtain ⟨-, Q', hQ'τ, hQ's⟩ := hsT
      rwa [Subtype.ext (hQs.trans hQ's.symm)]

/-! ### The polysimplicial complex of admissible parabolic subgroups -/

/-- The polysimplicial complex `(B₁, …, Bₙ)` of the component buildings
(KP Proposition 1.5.18(3)). -/
def restrictedComplex :
    Langlands.Geometry.Building.AbstractBuilding.PolysimplicialComplex (Component S) h.ComponentVertex where
  factor := h.componentComplex

/-- The product of the component simplices attached to a parabolic subgroup. -/
def restrictedBox (P : Subgroup G) : Set (∀ c, h.ComponentVertex c) :=
  Set.univ.pi fun c => h.componentFace c P

theorem componentFace_mem_faces {P : Subgroup G} (hP : IsAdmissibleParabolic B π S P)
    (c : Component S) : h.componentFace c P ∈ (h.componentComplex c).faces :=
  ⟨P, hP, rfl⟩

theorem restrictedBox_mem_facets {P : Subgroup G} (hP : IsAdmissibleParabolic B π S P) :
    h.restrictedBox P ∈ h.restrictedComplex.facets :=
  h.restrictedComplex.pi_mem_facets (h.componentFace_mem_faces hP)

omit [Finite S] in
/-- An admissible parabolic subgroup is the intersection of the component
vertices containing it. -/
theorem le_of_componentFace_subset {P P' : Subgroup G} (hP : IsAdmissibleParabolic B π S P)
    (hsub : ∀ c, h.componentFace c P ⊆ h.componentFace c P') : P' ≤ P := by
  obtain ⟨g, X, hX, rfl⟩ := h.exists_eq_conjugate_of_isAdmissibleParabolic hP
  intro x hx
  rw [mem_conjugateSubgroup_iff_inv]
  obtain ⟨w, hw⟩ := h.exists_mem_cell (g⁻¹ * x * g)
  refine ⟨w, ?_, hw⟩
  obtain ⟨m, hmlen, hmS, rfl⟩ := exists_word_length h.mul_self h.closure_eq w
  refine list_prod_mem fun y hy => Subgroup.subset_closure ?_
  by_contra hyX
  have hyS := hmS y hy
  let Q : h.ComponentVertex (componentOf ⟨y, hyS⟩) :=
    ⟨h.maximalParabolic g y, g, y, mem_componentSet_componentOf _, rfl⟩
  have hQ : Q ∈ h.componentFace (componentOf ⟨y, hyS⟩)
      (conjugateSubgroup g (h.standardParabolicSubgroup hX.1)) :=
    (h.conjugate_le_iff_of_isComponentVertex hX.1 g Q.2).mpr
      ⟨y, mem_componentSet_componentOf _, hyX, rfl⟩
  have hxQ : x ∈ h.maximalParabolic g y := hsub _ hQ hx
  rw [maximalParabolic, mem_conjugateSubgroup_iff_inv] at hxQ
  have hwY : m.prod ∈ Subgroup.closure (S \ {y}) :=
    (h.mem_standardParabolic_iff_of_mem_cell hw).mp hxQ
  exact (h.forall_mem_of_reduced_of_mem_closure Set.sdiff_subset hmS hmlen.symm hwY y hy).2 rfl

/-- Inclusion of products of simplices is reverse inclusion of admissible
parabolic subgroups. -/
theorem restrictedBox_subset_iff {P P' : Subgroup G} (hP : IsAdmissibleParabolic B π S P) :
    h.restrictedBox P ⊆ h.restrictedBox P' ↔ P' ≤ P := by
  rw [restrictedBox, restrictedBox,
    h.restrictedComplex.pi_subset_pi_iff (h.componentFace_mem_faces hP)]
  exact ⟨h.le_of_componentFace_subset hP, fun hle c Q hQ => hle.trans hQ⟩

/-- Every facet of the polysimplicial complex is the product attached to an
admissible parabolic subgroup (the surjectivity in KP Proposition 1.4.10). -/
theorem exists_restrictedBox_eq {F : Set (∀ c, h.ComponentVertex c)}
    (hF : F ∈ h.restrictedComplex.facets) :
    ∃ P, IsAdmissibleParabolic B π S P ∧ h.restrictedBox P = F := by
  obtain ⟨σ, hσ, rfl⟩ := hF
  choose P hP hPσ using hσ
  choose g X hX hgX using fun c => h.exists_eq_conjugate_of_isAdmissibleParabolic (hP c)
  obtain ⟨x, hx⟩ := h.exists_forall_inv_mul_mem g
  let Y : Set W := {s | ∃ c, s ∈ componentSet c ∧ s ∈ X c}
  have hmemY : ∀ {c : Component S} {s : W}, s ∈ componentSet c → (s ∈ Y ↔ s ∈ X c) := by
    intro c s hs
    constructor
    · rintro ⟨d, hd, hsd⟩
      rwa [eq_of_mem_componentSet hs hd]
    · intro hsX
      exact ⟨c, hs, hsX⟩
  have hY : IsAdmissibleType S Y := by
    refine isAdmissibleType_iff.mpr ⟨fun s ⟨c, hs, _⟩ => componentSet_subset c hs, fun c => ?_⟩
    obtain ⟨t, ht, htX⟩ := (isAdmissibleType_iff.mp (hX c)).2 c
    exact ⟨t, ht, fun htY => htX ((hmemY ht).mp htY)⟩
  refine ⟨_, h.isAdmissibleParabolic_conjugate_standard hY x,
    congrArg Set.univ.pi (funext fun c => ?_)⟩
  rw [hPσ c, hgX c]
  ext Q
  rw [mem_componentFace, mem_componentFace,
    h.conjugate_le_iff_of_isComponentVertex hY.1 x Q.2,
    h.conjugate_le_iff_of_isComponentVertex (hX c).1 (g c) Q.2]
  refine exists_congr fun s => and_congr_right fun hs => and_congr (not_congr (hmemY hs)) ?_
  have hk : (g c)⁻¹ * x ∈
      h.standardParabolicSubgroup (Set.sdiff_subset : S \ {s} ⊆ S) :=
    (h.standardParabolicSubgroup_le_iff Set.sdiff_subset Set.sdiff_subset).mpr
      (Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hs)) (hx c)
  have := h.maximalParabolic_mul_of_mem (g := g c) hk
  rw [mul_inv_cancel_left] at this
  rw [this]

/-- KP Proposition 1.5.18(3): the admissible parabolic subgroups, ordered by
reverse inclusion (the facets of the restricted building, KP Remark 1.5.7),
are order isomorphic to the facets of the polysimplicial complex of the
component buildings. -/
noncomputable def restrictedFacetOrderIso :
    {P : Subgroup G // IsAdmissibleParabolic B π S P}ᵒᵈ ≃o h.restrictedComplex.facets where
  toFun P := ⟨h.restrictedBox (OrderDual.ofDual P).1,
    h.restrictedBox_mem_facets (OrderDual.ofDual P).2⟩
  invFun F := OrderDual.toDual ⟨(h.exists_restrictedBox_eq F.2).choose,
    (h.exists_restrictedBox_eq F.2).choose_spec.1⟩
  left_inv P := by
    have hspec := (h.exists_restrictedBox_eq
      (h.restrictedBox_mem_facets (OrderDual.ofDual P).2)).choose_spec
    change (⟨_, hspec.1⟩ : {P : Subgroup G // IsAdmissibleParabolic B π S P}) =
      OrderDual.ofDual P
    exact Subtype.ext (le_antisymm
      ((h.restrictedBox_subset_iff (OrderDual.ofDual P).2).mp hspec.2.symm.subset)
      ((h.restrictedBox_subset_iff hspec.1).mp hspec.2.subset))
  right_inv F := Subtype.ext (h.exists_restrictedBox_eq F.2).choose_spec.2
  map_rel_iff' {P Q} := by
    change h.restrictedBox _ ⊆ h.restrictedBox _ ↔
      (OrderDual.ofDual Q).1 ≤ (OrderDual.ofDual P).1
    exact h.restrictedBox_subset_iff (OrderDual.ofDual P).2

@[simp] theorem restrictedFacetOrderIso_apply
    (P : {P : Subgroup G // IsAdmissibleParabolic B π S P}ᵒᵈ) :
    (h.restrictedFacetOrderIso P : Set (∀ c, h.ComponentVertex c)) =
      h.restrictedBox (OrderDual.ofDual P).1 :=
  rfl

end IsTitsSystem

end Langlands.Group
