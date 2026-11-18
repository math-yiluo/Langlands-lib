import Langlands.AlgebraicGeometry.EtaleLocalSystem
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Basic facts on étale local systems: coefficient groups -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

/-- On a preconnected space with a chosen point, locally constant functions to `M` are
identified with `M` by evaluation. -/
def locallyConstantAddEquiv (X : Type*) [TopologicalSpace X] [PreconnectedSpace X] (x : X)
    (M : Type*) [AddCommGroup M] : LocallyConstant X M ≃+ M where
  toFun f := f x
  invFun m := LocallyConstant.const X m
  left_inv f := (LocallyConstant.eq_const f x).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Sections of a constant sheaf over a preconnected object with a chosen point. -/
def constantSectionsAddEquiv {T : Scheme.{u}} (M : AddCommGrpCat.{v}) (V : Over T)
    [PreconnectedSpace V.left] (x : V.left) : (constant T M).obj (op V) ≃+ M :=
  (constantSections T M V).trans (locallyConstantAddEquiv V.left x M)

/-- Locally constant functions with values in isomorphic groups. -/
def locallyConstantCongrRight (X : Type*) [TopologicalSpace X] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (e : M ≃+ N) : LocallyConstant X M ≃+ LocallyConstant X N where
  toFun f := f.map e
  invFun f := f.map e.symm
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by ext; simp

/-- Isomorphic groups give isomorphic constant sheaves. -/
def constantCongr (T : Scheme.{u}) {M N : AddCommGrpCat.{v}} (e : M ≃+ N) :
    constant T M ≅ constant T N :=
  NatIso.ofComponents
    (fun V => AddEquiv.toAddCommGrpIso ((constantSections T M V.unop).trans
      ((locallyConstantCongrRight V.unop.left e).trans (constantSections T N V.unop).symm)))
    (by intros; rfl)

/-- If the constant sheaves of `M` and `N` are isomorphic, and some object `V` over the base has
a preconnected nonempty source, then `M` and `N` are isomorphic groups. -/
theorem nonempty_addEquiv_of_iso_of_object {T : Scheme.{u}} {M N : AddCommGrpCat.{v}}
    (e : constant T M ≅ constant T N) (V : Over T) [PreconnectedSpace V.left] (x : V.left) :
    Nonempty (M ≃+ N) :=
  ⟨(constantSectionsAddEquiv M V x).symm.trans
    ((e.app (op V)).addCommGroupIsoToAddEquiv.trans (constantSectionsAddEquiv N V x))⟩

/-- If the constant sheaves of `M` and `N` are isomorphic over a nonempty scheme, then `M` and
`N` are isomorphic groups. -/
theorem nonempty_addEquiv_of_iso {T : Scheme.{u}} [Nonempty T] {M N : AddCommGrpCat.{v}}
    (e : constant T M ≅ constant T N) : Nonempty (M ≃+ N) := by
  obtain ⟨t⟩ := ‹Nonempty T›
  have h : PreconnectedSpace (Spec (T.residueField t)) :=
    ⟨(Set.subsingleton_of_subsingleton (s := Set.univ)).isPreconnected⟩
  exact @nonempty_addEquiv_of_iso_of_object T M N e (Over.mk (T.fromSpecResidueField t)) h
    (default : Spec (T.residueField t))

variable {S : Scheme.{u}}

/-- An abelian presheaf `F` on schemes over `S` is *isotrivial* if it is an étale sheaf and it
becomes constant after restriction along a finite étale surjective morphism `p : S' ⟶ S`
(Conrad: "We call an étale sheaf on a scheme isotrivial if it becomes constant over a finite étale
cover"). The constant value group `M` is arbitrary. -/
def IsIsotrivial (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Prop :=
  IsEtaleSheaf F ∧ ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsFinite p ∧ Etale p ∧ Surjective p ∧
    ∃ M : AddCommGrpCat.{v}, Nonempty (restrict p F ≅ constant S' M)

/-- Every constant sheaf is isotrivial. -/
theorem isIsotrivial_constant (M : AddCommGrpCat.{v}) :
    IsIsotrivial.{u, v} (constant S M) :=
  ⟨isEtaleSheaf_constant S M, S, 𝟙 S, inferInstance, inferInstance, inferInstance, M,
    ⟨restrictConstantIso (𝟙 S) M⟩⟩

/-- Isotriviality is invariant under isomorphism of presheaves. -/
theorem IsIsotrivial.of_iso {F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} (e : F ≅ G)
    (hF : IsIsotrivial.{u, v} F) : IsIsotrivial.{u, v} G := by
  obtain ⟨hsh, S', p, h1, h2, h3, M, ⟨a⟩⟩ := hF
  exact ⟨(isEtaleSheaf_iff_of_iso e).1 hsh, S', p, h1, h2, h3, M,
    ⟨(restrictIso p e).symm ≪≫ a⟩⟩

/-- Two members of a trivializing étale cover whose images meet have isomorphic coefficient
groups. -/
theorem nonempty_addEquiv_of_apply_eq {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {M N : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y N) (a : X) (b : Y)
    (hab : f a = g b) : Nonempty (M ≃+ N) := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  have : Nonempty ↥(pullback f g) := ⟨z⟩
  exact nonempty_addEquiv_of_iso
    ((restrictConstantIso (pullback.fst f g) M).symm ≪≫
      restrictIso _ ef.symm ≪≫ (restrictCompIso f _ F).symm ≪≫
      restrictCongrIso pullback.condition F ≪≫ restrictCompIso g _ F ≪≫
      restrictIso _ eg ≪≫ restrictConstantIso _ N)

/-- **One coefficient group on a connected base.** If `S` is connected, a finitely generated
local system on `S` is constant with one and the same finitely generated group `M` on every
member of some étale cover. -/
theorem exists_common_model [ConnectedSpace S] {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (hF : IsFinitelyGeneratedLocallyConstant.{u, v} F) :
    ∃ M : AddCommGrpCat.{v}, AddGroup.FG M ∧
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ i : 𝒰.I₀, Nonempty (restrict (𝒰.f i) F ≅ constant (𝒰.X i) M) := by
  classical
  obtain ⟨-, 𝒰, h𝒰⟩ := hF
  choose M hM e using h𝒰
  obtain ⟨s₀⟩ := ConnectedSpace.toNonempty (α := S)
  choose idx hidx using ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1
  let i₀ := idx s₀
  have hopen : ∀ i, IsOpen (Set.range (𝒰.f i)) := fun i => by
    have := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap.isOpen_range
  let good : 𝒰.I₀ → Prop := fun i => Nonempty (M i ≃+ M i₀)
  let W₁ : Set S := ⋃ i ∈ {i | good i}, Set.range (𝒰.f i)
  let W₂ : Set S := ⋃ i ∈ {i | ¬ good i}, Set.range (𝒰.f i)
  have h1 : IsOpen W₁ := isOpen_biUnion fun i _ => hopen i
  have h2 : IsOpen W₂ := isOpen_biUnion fun i _ => hopen i
  have hcompl : W₁ᶜ = W₂ := by
    ext s
    simp only [W₁, W₂, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hs
      refine ⟨idx s, fun hg => hs ⟨idx s, hg, hidx s⟩, hidx s⟩
    · rintro ⟨j, hj, b, hb⟩ ⟨i, hi, a, ha⟩
      obtain ⟨ej⟩ := e j
      obtain ⟨ei⟩ := e i
      obtain ⟨φ⟩ := nonempty_addEquiv_of_apply_eq ej ei b a (hb.trans ha.symm)
      obtain ⟨ψ⟩ := hi
      exact hj ⟨φ.trans ψ⟩
  have hW₁ : W₁ = Set.univ := by
    have hclopen : IsClopen W₁ := ⟨by rw [← isOpen_compl_iff, hcompl]; exact h2, h1⟩
    refine hclopen.eq_univ ⟨s₀, ?_⟩
    simp only [W₁, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨i₀, ⟨AddEquiv.refl _⟩, hidx s₀⟩
  refine ⟨M i₀, hM i₀, Scheme.Cover.mkOfCovers {i : 𝒰.I₀ // good i} (fun j => 𝒰.X j.1)
    (fun j => 𝒰.f j.1) ?_ (fun j => 𝒰.map_prop j.1), ?_⟩
  · intro s
    have hs : s ∈ W₁ := hW₁ ▸ Set.mem_univ s
    simp only [W₁, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hs
    obtain ⟨i, hi, a, ha⟩ := hs
    exact ⟨⟨i, hi⟩, a, ha⟩
  · intro j
    obtain ⟨ej⟩ := e j.1
    obtain ⟨φ⟩ := j.2
    exact ⟨ej ≪≫ constantCongr _ φ⟩

end Langlands.AlgebraicGeometry.EtaleLocalSystem
