import Langlands.Cohomology.Profinite.Comparison.FilteredHomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Group cohomology of restricted products; naturality of the connecting map

Let `G` be a finite group and `A` a representation of `G` which is the restricted product of a
family `P i` with respect to subrepresentations `U i ⊆ P i`, through morphisms `π i : A ⟶ P i`
(`IsRestrictedProduct π j`): an element of `A` is determined by its components, its components lie
in `U i` for all but finitely many `i`, and every such family of components comes from an element.
If `Hⁿ⁺¹(G, U i) = 0` for all but finitely many `i`, a class of `Hⁿ⁺¹(G, A)` whose components in
every `Hⁿ⁺¹(G, P i)` vanish is zero (`IsRestrictedProduct.eq_zero_of_map_eq_zero`), and the components
of a class are nonzero for finitely many `i` only (`IsRestrictedProduct.finite_map_ne_zero`). The
proof is on cochains: an `n+1`-cochain of a finite group takes finitely many values, so its
components lie in `U i` outside a finite set of indices; there the primitives are chosen in `U i`,
elsewhere in `P i`, and the primitives assemble to a cochain of `A`.

The file also proves, for the group cohomology of Mathlib (`groupCohomology`):

* the naturality of the connecting homomorphism for a change of group together with a morphism of
  short exact sequences of coefficients (`groupCohomology_δ_comp_map`);
* the map along a bijective homomorphism and a bijective coefficient map is bijective
  (`bijective_groupCohomology_map`).
-/

namespace Langlands.Cohomology

open CategoryTheory Limits groupCohomology

universe u v

section Cochains

variable {k G : Type u} [CommRing k] [Group G]

/-- The differential of inhomogeneous cochains commutes with a morphism of representations. -/
theorem hom_inhomogeneousCochains_d_apply {A B : Rep.{u} k G} (φ : A ⟶ B) {n : ℕ}
    (f : (Fin n → G) → A) (g : Fin (n + 1) → G) :
    φ.hom (inhomogeneousCochains.d A n f g) =
      inhomogeneousCochains.d B n (fun x => φ.hom (f x)) g := by
  simp only [inhomogeneousCochains.d_hom_apply, map_add, map_sum, map_smul, Rep.hom_comm_apply]

/-- A cocycle of degree `n + 1` has zero class exactly when it is the differential of an
`n`-cochain. -/
theorem π_eq_zero_iff_exists_d_eq {A : Rep.{u} k G} {n : ℕ} (z : cocycles A (n + 1)) :
    π A (n + 1) z = 0 ↔ ∃ β : (Fin n → G) → A, inhomogeneousCochains.d A n β = iCocycles A (n + 1) z := by
  have key : ∀ m (hm : (ComplexShape.up ℕ).prev (n + 1) = m),
      (∃ w : (inhomogeneousCochains A).X ((ComplexShape.up ℕ).prev (n + 1)),
          ((inhomogeneousCochains A).d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom w =
            (iCocycles A (n + 1)).hom z) ↔
        ∃ w : (inhomogeneousCochains A).X m,
          ((inhomogeneousCochains A).d m (n + 1)).hom w = (iCocycles A (n + 1)).hom z := by
    intro m hm
    subst hm
    rfl
  have h := ProfiniteCohomology.homologyπ_eq_zero_iff (inhomogeneousCochains A) z
  rw [key n (CochainComplex.prev_nat_succ n)] at h
  simp only [CochainComplex.of_d] at h
  exact h

/-- The class of the cocycle made from `f` is zero when `f` is a differential. -/
theorem π_cocyclesMk_eq_zero {A : Rep.{u} k G} {n : ℕ} (f : (Fin (n + 1) → G) → A)
    (hf : inhomogeneousCochains.d A (n + 1) f = 0) (β : (Fin n → G) → A)
    (hβ : inhomogeneousCochains.d A n β = f) :
    π A (n + 1) (cocyclesMk f hf) = 0 :=
  (π_eq_zero_iff_exists_d_eq _).2 ⟨β, by rw [iCocycles_mk, hβ]⟩

/-- The `n+1`-cochain underlying the image of a cocycle under a morphism of representations is the
composite with the morphism. -/
theorem iCocycles_cocyclesMap_id_apply {A B : Rep.{u} k G} (φ : A ⟶ B) {n : ℕ}
    (z : cocycles A n) (g : Fin n → G) :
    iCocycles B n (cocyclesMap (MonoidHom.id G) φ n z) g = φ.hom (iCocycles A n z g) := by
  have h := ProfiniteCohomology.iCycles_cyclesMap_apply (cochainsMap (MonoidHom.id G) φ) n z
  exact congrFun h g

/-- The image of the class of a cocycle under a morphism of representations is the class of the
image cocycle. -/
theorem map_id_π_apply {A B : Rep.{u} k G} (φ : A ⟶ B) {n : ℕ} (z : cocycles A n) :
    groupCohomology.map (MonoidHom.id G) φ n (π A n z) =
      π B n (cocyclesMap (MonoidHom.id G) φ n z) :=
  ProfiniteCohomology.homologyMap_homologyπ_apply (cochainsMap (MonoidHom.id G) φ) n z

end Cochains

section RestrictedProduct

variable {k G : Type u} [CommRing k] [Group G] {ι : Type v}
  {A : Rep.{u} k G} {P U : ι → Rep.{u} k G}

variable (π : ∀ i, A ⟶ P i) (j : ∀ i, U i ⟶ P i)

/-- `A` is the restricted product of the representations `P i` with respect to the
subrepresentations `j i : U i ⟶ P i`, through the components `π i : A ⟶ P i`. -/
structure IsRestrictedProduct : Prop where
  /-- Each `U i` is a subrepresentation of `P i`. -/
  injective : ∀ i, Function.Injective (j i).hom
  /-- An element is determined by its components. -/
  eq_zero : ∀ a : A, (∀ i, (π i).hom a = 0) → a = 0
  /-- The components of an element lie in `U i` for all but finitely many `i`. -/
  finite : ∀ a : A, {i | (π i).hom a ∉ Set.range (j i).hom}.Finite
  /-- A family of components lying in `U i` for all but finitely many `i` comes from an element. -/
  exists_eq : ∀ p : ∀ i, P i, {i | p i ∉ Set.range (j i).hom}.Finite →
    ∃ a : A, ∀ i, (π i).hom a = p i

variable {π j}

/-- **Cohomology of a restricted product.** Let `G` be finite and `A` the restricted product of the
`P i` with respect to the `U i`. If `Hⁿ⁺¹(G, U i) = 0` for all but finitely many `i`, then a class of
`Hⁿ⁺¹(G, A)` whose image in every `Hⁿ⁺¹(G, P i)` is zero is zero. -/
theorem IsRestrictedProduct.eq_zero_of_map_eq_zero [Finite G] (h : IsRestrictedProduct π j)
    (n : ℕ) (hU : {i | ¬ IsZero (groupCohomology (U i) (n + 1))}.Finite)
    (x : groupCohomology A (n + 1))
    (hx : ∀ i, groupCohomology.map (MonoidHom.id G) (π i) (n + 1) x = 0) : x = 0 := by
  classical
  induction x using groupCohomology_induction_on with | h z => ?_
  set f : (Fin (n + 1) → G) → A := iCocycles A (n + 1) z with hfdef
  have hf : inhomogeneousCochains.d A (n + 1) f = 0 := by
    have := ProfiniteCohomology.iCycles_d_apply (inhomogeneousCochains A) (n + 1) (n + 1 + 1) z
    simpa only [CochainComplex.of_d] using this
  -- the indices where some value of `f` has a component outside `U i`, or `Hⁿ⁺¹(U i) ≠ 0`
  let T : Set ι := (⋃ g : Fin (n + 1) → G, {i | (π i).hom (f g) ∉ Set.range (j i).hom}) ∪
    {i | ¬ IsZero (groupCohomology (U i) (n + 1))}
  have hT : T.Finite := (Set.finite_iUnion fun g => h.finite (f g)).union hU
  -- primitives of the components, in `U i` outside `T`
  have hprim : ∀ i, ∃ β : (Fin n → G) → P i,
      inhomogeneousCochains.d (P i) n β = (fun g => (π i).hom (f g)) ∧
        (i ∉ T → ∀ g, β g ∈ Set.range (j i).hom) := by
    intro i
    by_cases hi : i ∈ T
    · have h0 := hx i
      rw [map_id_π_apply, π_eq_zero_iff_exists_d_eq] at h0
      obtain ⟨β, hβ⟩ := h0
      refine ⟨β, ?_, fun h' => absurd hi h'⟩
      rw [hβ]
      funext g
      exact iCocycles_cocyclesMap_id_apply (π i) z g
    · have hval : ∀ g, (π i).hom (f g) ∈ Set.range (j i).hom := by
        intro g
        by_contra hg
        exact hi (Or.inl (Set.mem_iUnion.2 ⟨g, hg⟩))
      have hzero : IsZero (groupCohomology (U i) (n + 1)) := by
        by_contra hz
        exact hi (Or.inr hz)
      choose f' hf' using hval
      have hdf' : inhomogeneousCochains.d (U i) (n + 1) f' = 0 := by
        funext g
        apply h.injective i
        rw [hom_inhomogeneousCochains_d_apply, Pi.zero_apply, map_zero]
        have hcomp : (fun x => (j i).hom (f' x)) = fun x => (π i).hom (f x) := funext hf'
        rw [hcomp, ← hom_inhomogeneousCochains_d_apply, hf]
        exact map_zero _
      have hcl : groupCohomology.π (U i) (n + 1) (cocyclesMk f' hdf') = 0 :=
        (ModuleCat.isZero_iff_subsingleton.1 hzero).elim _ _
      rw [π_eq_zero_iff_exists_d_eq, iCocycles_mk] at hcl
      obtain ⟨β', hβ'⟩ := hcl
      refine ⟨fun g => (j i).hom (β' g), ?_, fun _ g => ⟨β' g, rfl⟩⟩
      funext g
      rw [← hom_inhomogeneousCochains_d_apply, hβ', hf']
  choose β hβd hβU using hprim
  -- assemble the primitives
  have hb : ∀ g : Fin n → G, ∃ a : A, ∀ i, (π i).hom a = β i g := fun g =>
    h.exists_eq (fun i => β i g) (hT.subset fun i hi => by
      by_contra hiT
      exact hi (hβU i hiT g))
  choose b hb using hb
  refine (π_eq_zero_iff_exists_d_eq z).2 ⟨b, ?_⟩
  funext g
  rw [← sub_eq_zero]
  apply h.eq_zero
  intro i
  rw [map_sub, hom_inhomogeneousCochains_d_apply, sub_eq_zero]
  have hbi : (fun x => (π i).hom (b x)) = β i := funext fun x => hb x i
  rw [hbi, hβd i]

/-- **Finite support.** Let `G` be finite and `A` the restricted product of the `P i` with respect
to the `U i`. If `Hⁿ⁺¹(G, U i) = 0` for all but finitely many `i`, the image of a class of
`Hⁿ⁺¹(G, A)` in `Hⁿ⁺¹(G, P i)` vanishes for all but finitely many `i`. -/
theorem IsRestrictedProduct.finite_map_ne_zero [Finite G] (h : IsRestrictedProduct π j)
    (n : ℕ) (hU : {i | ¬ IsZero (groupCohomology (U i) (n + 1))}.Finite)
    (x : groupCohomology A (n + 1)) :
    {i | groupCohomology.map (MonoidHom.id G) (π i) (n + 1) x ≠ 0}.Finite := by
  classical
  induction x using groupCohomology_induction_on with | h z => ?_
  set f : (Fin (n + 1) → G) → A := iCocycles A (n + 1) z with hfdef
  let T : Set ι := (⋃ g : Fin (n + 1) → G, {i | (π i).hom (f g) ∉ Set.range (j i).hom}) ∪
    {i | ¬ IsZero (groupCohomology (U i) (n + 1))}
  have hT : T.Finite := (Set.finite_iUnion fun g => h.finite (f g)).union hU
  refine hT.subset fun i hi => ?_
  by_contra hiT
  apply hi
  have hval : ∀ g, (π i).hom (f g) ∈ Set.range (j i).hom := by
    intro g
    by_contra hg
    exact hiT (Or.inl (Set.mem_iUnion.2 ⟨g, hg⟩))
  have hzero : IsZero (groupCohomology (U i) (n + 1)) := by
    by_contra hz
    exact hiT (Or.inr hz)
  have hf : inhomogeneousCochains.d A (n + 1) f = 0 := by
    have := ProfiniteCohomology.iCycles_d_apply (inhomogeneousCochains A) (n + 1) (n + 1 + 1) z
    simpa only [CochainComplex.of_d] using this
  choose f' hf' using hval
  have hdf' : inhomogeneousCochains.d (U i) (n + 1) f' = 0 := by
    funext g
    apply h.injective i
    rw [hom_inhomogeneousCochains_d_apply, Pi.zero_apply, map_zero]
    have hcomp : (fun x => (j i).hom (f' x)) = fun x => (π i).hom (f x) := funext hf'
    rw [hcomp, ← hom_inhomogeneousCochains_d_apply, hf]
    exact map_zero _
  have hcl : groupCohomology.π (U i) (n + 1) (cocyclesMk f' hdf') = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 hzero).elim _ _
  rw [π_eq_zero_iff_exists_d_eq, iCocycles_mk] at hcl
  obtain ⟨β', hβ'⟩ := hcl
  rw [map_id_π_apply, π_eq_zero_iff_exists_d_eq]
  refine ⟨fun g => (j i).hom (β' g), ?_⟩
  funext g
  rw [← hom_inhomogeneousCochains_d_apply, hβ', hf', iCocycles_cocyclesMap_id_apply]

end RestrictedProduct

noncomputable section

section Naturality

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (f : G' →* G)
  {X : ShortComplex (Rep.{u} k G)} {Y : ShortComplex (Rep.{u} k G')}
  (α : X.map (Rep.resFunctor f) ⟶ Y)

/-- The morphism of short complexes of inhomogeneous cochain complexes induced by a change of group
`f` and a morphism `α` of short complexes of coefficients. -/
def inhomogeneousCochainsShortComplexMapAlong :
    X.map (groupCohomology.cochainsFunctor k G) ⟶ Y.map (groupCohomology.cochainsFunctor k G') where
  τ₁ := groupCohomology.cochainsMap f α.τ₁
  τ₂ := groupCohomology.cochainsMap f α.τ₂
  τ₃ := groupCohomology.cochainsMap f α.τ₃
  comm₁₂ := by
    ext n x : 3
    funext g
    exact congrArg (fun ψ => ψ.hom (x (f ∘ g))) α.comm₁₂
  comm₂₃ := by
    ext n x : 3
    funext g
    exact congrArg (fun ψ => ψ.hom (x (f ∘ g))) α.comm₂₃

/-- **Naturality of the connecting homomorphism** along a change of group: for short exact
sequences `X` of `G`-modules and `Y` of `G'`-modules and a morphism `α : Res_f X ⟶ Y`, the square
`δ_X ≫ map f α₁ = map f α₃ ≫ δ_Y` commutes. -/
@[reassoc]
theorem groupCohomology_δ_comp_map (hX : X.ShortExact) (hY : Y.ShortExact) (i j : ℕ)
    (hij : i + 1 = j) :
    groupCohomology.δ hX i j hij ≫ groupCohomology.map f α.τ₁ j =
      groupCohomology.map f α.τ₃ i ≫ groupCohomology.δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (inhomogeneousCochainsShortComplexMapAlong f α)
    (groupCohomology.map_cochainsFunctor_shortExact hX)
    (groupCohomology.map_cochainsFunctor_shortExact hY) i j hij

end Naturality

end

section Bijective

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The map on group cohomology along a bijective homomorphism and a bijective coefficient map is
bijective. -/
theorem bijective_groupCohomology_map {A : Rep.{u} k G} {B : Rep.{u} k H} (f : H →* G)
    (hf : Function.Bijective f) (φ : Rep.res f A ⟶ B) (hφ : Function.Bijective φ.hom) (n : ℕ) :
    Function.Bijective (groupCohomology.map f φ n) := by
  let e : G ≃* H := (MulEquiv.ofBijective f hf).symm
  let e' : A.V ≃ₗ[k] B.V := LinearEquiv.ofBijective φ.hom.toLinearMap hφ
  have he : ∀ g, e' ∘ₗ A.ρ g = B.ρ (e g) ∘ₗ e' := by
    intro g
    ext a
    have hfe : f (e g) = g := (MulEquiv.ofBijective f hf).apply_symm_apply g
    change φ.hom (A.ρ g a) = B.ρ (e g) (φ.hom a)
    rw [← Rep.hom_comm_apply φ (e g) a]
    change φ.hom (A.ρ g a) = φ.hom (A.ρ (f (e g)) a)
    rw [hfe]
  have hmap : groupCohomology.map f φ n = (groupCohomology.mapIso e e' he n).hom :=
    groupCohomology.map_congr (MonoidHom.ext fun _ => rfl) rfl n
  rw [hmap]
  exact (groupCohomology.mapIso e e' he n).toLinearEquiv.bijective

end Bijective

end Langlands.Cohomology
