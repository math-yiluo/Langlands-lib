import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Langlands.Cohomology.FiniteClosedSupportSheafProof

/-! # Global sections of a module with finite closed support, localized at its points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} (s : Y ⟶ Spec R)

/-- Restriction of relative global sections to an open `U`, as an `R`-linear map. -/
def sectionsRestrict (G : Y.Modules) (U : Y.Opens) :
    (relativeGlobalSections s).obj G ⟶
      (relativeGlobalSections (U.ι ≫ s)).obj ((Scheme.Modules.restrictFunctor U.ι).obj G) :=
  (relativeGlobalSections s).map ((Scheme.Modules.restrictAdjunction U.ι).unit.app G) ≫
    ((relativeGlobalSectionsCompIso U.ι s).app _).hom

/-- The underlying map of `sectionsRestrict` is the restriction map of the abelian presheaf. -/
lemma sectionsRestrict_apply (G : Y.Modules) (U : Y.Opens)
    (x : (relativeGlobalSections s).obj G) :
    (sectionsRestrict s G U).hom x =
      G.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op x := by
  rfl

/-- The restrictions of relative global sections to a family of opens indexed by a finite set
of points. -/
def sectionsRestrictPi (G : Y.Modules) (S : Finset Y) (V : Y → Y.Opens) :
    (relativeGlobalSections s).obj G →ₗ[R] ((x : S) →
      (relativeGlobalSections ((V x).ι ≫ s)).obj
        ((Scheme.Modules.restrictFunctor (V x).ι).obj G)) :=
  LinearMap.pi fun x => (sectionsRestrict s G (V x)).hom

/-- A finite set of closed points is closed. -/
lemma isClosed_finset_of_isClosed_singleton (S : Finset Y)
    (hcl : ∀ x ∈ S, IsClosed ({x} : Set Y)) : IsClosed (S : Set Y) := by
  have := S.finite_toSet.isClosed_biUnion (f := fun x => ({x} : Set Y)) fun x hx => hcl x hx
  simpa only [Set.biUnion_of_singleton] using this

/-- **Localization of global sections at finitely many points.** Let `G` be a module whose
nonzero stalks lie in a finite set `S` of closed points, and for every `x ∈ S` let `V x` be an
open neighbourhood of `x` meeting `S` only in `x`. Then restriction to the opens `V x` is a
bijection from the relative global sections of `G` onto the product of the relative global
sections of the restrictions of `G` to the `V x`. -/
theorem sectionsRestrictPi_bijective (G : Y.Modules) (S : Finset Y)
    (hcl : ∀ x ∈ S, IsClosed ({x} : Set Y)) (hsupp : stalkSupport G ⊆ S)
    (V : Y → Y.Opens) (hV : ∀ x ∈ S, x ∈ V x)
    (hVS : ∀ x ∈ S, ∀ y ∈ S, y ∈ V x → y = x) :
    Function.Bijective (sectionsRestrictPi s G S V) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} Y := (SheafOfModules.toSheaf Y.ringCatSheaf).obj G
  have hz : ∀ y, y ∉ (S : Set Y) →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj F.obj) := fun y hy => by
    by_contra h
    exact hy (hsupp h)
  have hzero : ∀ {O : Y.Opens}, (∀ y ∈ O, y ∉ (S : Set Y)) → ∀ t : F.1.obj (op O), t = 0 :=
    fun hO t => Langlands.Cohomology.FiniteClosedSupportSheaf.eq_zero_of_forall_not_mem F hz hO t
  let C : Y.Opens := ⟨(S : Set Y)ᶜ, (isClosed_finset_of_isClosed_singleton S hcl).isOpen_compl⟩
  let W : Option S → Y.Opens := fun i => Option.elim i C (fun x => (V x).ι ''ᵁ ⊤)
  have hW : ∀ x : S, W (some x) = V x := fun x => Scheme.Opens.ι_image_top (V x)
  have hcover : (⊤ : Y.Opens) ≤ iSup W := by
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ S
    · refine ⟨some ⟨y, hy⟩, ?_⟩
      rw [hW]
      exact hV y hy
    · exact ⟨none, hy⟩
  have hdisj : ∀ i j : Option S, i ≠ j → ∀ y ∈ W i ⊓ W j, y ∉ (S : Set Y) := by
    intro i j hij y hy hyS
    obtain ⟨hyi, hyj⟩ := hy
    cases i with
    | none => exact hyi hyS
    | some x =>
      cases j with
      | none => exact hyj hyS
      | some x' =>
        rw [hW] at hyi
        rw [hW] at hyj
        have h1 := hVS x x.2 y hyS hyi
        have h2 := hVS x' x'.2 y hyS hyj
        exact hij (congrArg some (Subtype.ext (h1.symm.trans h2)))
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    apply F.eq_of_locally_eq' W ⊤ (fun i => homOfLE le_top) hcover t 0
    intro i
    rw [map_zero]
    cases i with
    | none => exact hzero (fun y hy => hy) _
    | some x => exact congrFun ht x
  · intro u
    let sf : ∀ i : Option S, F.1.obj (op (W i)) := fun i =>
      match i with
      | none => 0
      | some x => u x
    have hcompat : TopCat.Presheaf.IsCompatible F.1 W sf := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rfl
      · rw [hzero (hdisj i j hij) (F.1.map _ (sf i)), hzero (hdisj i j hij) (F.1.map _ (sf j))]
    obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcover sf hcompat
    exact ⟨t, funext fun x => ht (some x)⟩

end Langlands.AlgebraicGeometry.Modules.DerivedSections
