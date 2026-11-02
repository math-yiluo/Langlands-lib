import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.Descent.FppfSeparatedLocallyQuasiFiniteDescentStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Representable diagonal from a kernel pair locally of finite type

Let `Q` be an fppf sheaf over `S` with a locally surjective map `a` from a scheme `U` whose kernel
pair is represented by `t s : R ⟶ U`, with `t` locally of finite type. Given fppf descent of
separated, locally quasi-finite schemes of locally finite type, the diagonal of `Q` is
representable: the equalizer of two sections of `Q` over a scheme `V` becomes, after base change
to a covering sieve of `V` on which both sections lift to `U`, a base change of the monomorphism
`(t, s) : R ⟶ U × U`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPair

variable {S : Scheme.{u}}

/-- The subfunctor of the points of `V` along which two sections of `F` over `V` agree. -/
def eqLocus {F : Presheaf S} {V : Over S} (x y : F.obj (op V)) :
    Subfunctor ((schemeYoneda S).obj V) where
  obj T := {g | F.map g.down.op x = F.map g.down.op y}
  map {T T'} f g hg := by
    change F.map (f.unop ≫ g.down).op x = F.map (f.unop ≫ g.down).op y
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hg]

theorem mem_eqLocus_iff {F : Presheaf S} {V T : Over S} (x y : F.obj (op V))
    (g : ULift.{u + 1} (T ⟶ V)) :
    g ∈ (eqLocus x y).obj (op T) ↔ F.map g.down.op x = F.map g.down.op y :=
  Iff.rfl

/-- The points of a scheme over `S` form an fppf sheaf of types. -/
theorem isSheaf_schemeYoneda (V : Over S) :
    Presieve.IsSheaf (fppfTopology S) ((schemeYoneda S).obj V) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((schemeSheaf S).obj V).property

/-- The equalizer locus of two sections of an fppf sheaf is an fppf sheaf. -/
theorem isSheaf_eqLocus (Q : FppfSheaf S) {V : Over S} (x y : Q.obj.obj (op V)) :
    Presieve.IsSheaf (fppfTopology S) (eqLocus x y).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (isSheaf_schemeYoneda V)]
  intro T g hg
  have hQ := ((isSheaf_iff_isSheaf_of_type _ _).1 Q.property).isSeparated _ hg
  apply hQ.ext
  intro T' u hu
  have hu' : Q.obj.map (u ≫ g.down).op x = Q.obj.map (u ≫ g.down).op y := hu
  rwa [op_comp, Functor.map_comp_apply, Functor.map_comp_apply] at hu'

/-- The equalizer locus of two sections of an fppf sheaf, as an fppf sheaf. -/
def eqLocusSheaf (Q : FppfSheaf S) {V : Over S} (x y : Q.obj.obj (op V)) : FppfSheaf S :=
  ⟨(eqLocus x y).toFunctor, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_eqLocus Q x y)⟩

/-- Two points of schemes with equal images under maps to a presheaf give equal composites. -/
theorem map_comp_eq_map_comp_of_app_eq {F : Presheaf S} {U U' T : Over S}
    (α : (schemeYoneda S).obj U ⟶ F) (β : (schemeYoneda S).obj U' ⟶ F) {f : T ⟶ U}
    {f' : T ⟶ U'} (e : α.app (op T) ⟨f⟩ = β.app (op T) ⟨f'⟩) :
    (schemeYoneda S).map f ≫ α = (schemeYoneda S).map f' ≫ β := by
  ext T' ⟨k⟩
  have h₁ := NatTrans.naturality_apply α k.op ⟨f⟩
  have h₂ := NatTrans.naturality_apply β k.op ⟨f'⟩
  rw [e] at h₁
  exact h₁.trans h₂.symm

/-- Two points of `U` with equal images under a map to a presheaf give equal composites. -/
theorem map_comp_eq_of_app_eq {F : Presheaf S} {U T : Over S}
    (α : (schemeYoneda S).obj U ⟶ F) {f f' : T ⟶ U}
    (e : α.app (op T) ⟨f⟩ = α.app (op T) ⟨f'⟩) :
    (schemeYoneda S).map f ≫ α = (schemeYoneda S).map f' ≫ α :=
  map_comp_eq_map_comp_of_app_eq α α e

/-- A monomorphism in `Over S` stays a monomorphism of the underlying schemes. -/
theorem mono_left_of_map_mono {X Y : Over S} (f : X ⟶ Y) [Mono ((schemeYoneda S).map f)] :
    Mono f.left := by
  have : Mono f := (schemeYoneda S).mono_of_mono_map inferInstance
  infer_instance

variable (hD : FppfSeparatedLocallyQuasiFiniteDescentStatement.{u})
  {Q : FppfSheaf S} {U R : Over S} (a : (schemeYoneda S).obj U ⟶ Q.obj)
  [Presheaf.IsLocallySurjective (fppfTopology S) a] {t s : R ⟶ U}
  (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)

omit [Presheaf.IsLocallySurjective (fppfTopology S) a] in
include h in
/-- The kernel pair `(t, s) : R ⟶ U × U` is a monomorphism. -/
theorem mono_prodLift_of_isPullback : Mono (prod.lift t s) := by
  constructor
  intro Z r r' e
  exact EtaleEquivalenceRelation.hom_ext_of_isPullback h
    (by simpa using congrArg (· ≫ prod.fst) e) (by simpa using congrArg (· ≫ prod.snd) e)

omit [Presheaf.IsLocallySurjective (fppfTopology S) a] in
include h in
/-- After base change along a morphism `g : T ⟶ V` on which two sections `x y` of `Q` lift to
points `τ₁ τ₂` of `U`, their equalizer locus is represented by the base change of
`(t, s) : R ⟶ U × U` along `(τ₁, τ₂)`, which is a monomorphism and locally of finite type when
`t` is. -/
theorem exists_isPullback_eqLocus (ht : LocallyOfFiniteType t.left) {V T : Over S}
    (x y : Q.obj.obj (op V)) (g : T ⟶ V) (τ₁ τ₂ : T ⟶ U)
    (hτ₁ : a.app (op T) ⟨τ₁⟩ = Q.obj.map g.op x) (hτ₂ : a.app (op T) ⟨τ₂⟩ = Q.obj.map g.op y) :
    ∃ (X' : Over S) (x' : X' ⟶ T) (a' : (schemeYoneda S).obj X' ⟶ (eqLocus x y).toFunctor),
      IsPullback a' ((schemeYoneda S).map x') (eqLocus x y).ι ((schemeYoneda S).map g) ∧
        IsSeparated x'.left ∧ LocallyQuasiFinite x'.left ∧ LocallyOfFiniteType x'.left := by
  have hj : Mono (prod.lift t s) := mono_prodLift_of_isPullback a h
  let X' := Limits.pullback (prod.lift τ₁ τ₂) (prod.lift t s)
  let x' : X' ⟶ T := Limits.pullback.fst _ _
  let r' : X' ⟶ R := Limits.pullback.snd _ _
  have hX : IsPullback x' r' (prod.lift τ₁ τ₂) (prod.lift t s) := IsPullback.of_hasPullback _ _
  have e₁ : x' ≫ τ₁ = r' ≫ t := by
    simpa using congrArg (· ≫ prod.fst) hX.w
  have e₂ : x' ≫ τ₂ = r' ≫ s := by
    simpa using congrArg (· ≫ prod.snd) hX.w
  -- naturality of `a` on points
  have ha : ∀ {T' : Over S} (k : T' ⟶ T) (τ : T ⟶ U),
      a.app (op T') ⟨k ≫ τ⟩ = Q.obj.map k.op (a.app (op T) ⟨τ⟩) := fun k τ ↦
    NatTrans.naturality_apply a k.op ⟨τ⟩
  have haw : ∀ {T' : Over S} (k : T' ⟶ R), a.app (op T') ⟨k ≫ t⟩ = a.app (op T') ⟨k ≫ s⟩ :=
    fun k ↦ congrArg (fun φ ↦ φ.app _ ⟨k⟩) h.w
  have hmem : ∀ {T' : Over S} (z : T' ⟶ X'),
      Q.obj.map (z ≫ x' ≫ g).op x = Q.obj.map (z ≫ x' ≫ g).op y := by
    intro T' z
    rw [← Category.assoc, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      ← hτ₁, ← hτ₂, ← ha, ← ha, Category.assoc, Category.assoc, e₁, e₂, ← Category.assoc,
      ← Category.assoc, haw]
  let a' : (schemeYoneda S).obj X' ⟶ (eqLocus x y).toFunctor :=
    Subfunctor.lift ((schemeYoneda S).map (x' ≫ g)) (by
      rintro T' _ ⟨z, rfl⟩
      exact hmem z.down)
  have hmono : Mono x'.left := by
    have : Mono x' := inferInstance
    infer_instance
  have hlft : LocallyOfFiniteType x'.left := by
    have hjl : LocallyOfFiniteType (prod.lift t s).left := by
      have : LocallyOfFiniteType ((prod.lift t s).left ≫ (prod.fst : U ⨯ U ⟶ U).left) := by
        rw [← Over.comp_left, prod.lift_fst]
        exact ht
      exact locallyOfFiniteType_of_comp _ (prod.fst : U ⨯ U ⟶ U).left
    exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (hX.map (Over.forget S)).flip hjl
  refine ⟨X', x', a', ?_, inferInstance, inferInstance, hlft⟩
  refine IsPullback.of_forall_isPullback_app fun T' ↦ ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · have : a' ≫ (eqLocus x y).ι = (schemeYoneda S).map (x' ≫ g) := Subfunctor.lift_ι _ _
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, this, Functor.map_comp]
  · rintro ⟨z⟩ ⟨z'⟩ ⟨-, hz⟩
    have hz' : z ≫ x' = z' ≫ x' := congrArg ULift.down hz
    exact congrArg ULift.up ((cancel_mono x').1 hz')
  · rintro ⟨⟨g₁⟩, hg₁⟩ ⟨w⟩ hw
    have hw' : g₁ = w ≫ g := congrArg ULift.down hw
    subst hw'
    have hg₁' : Q.obj.map (w ≫ g).op x = Q.obj.map (w ≫ g).op y := hg₁
    obtain ⟨r, hr₁, hr₂⟩ := EtaleEquivalenceRelation.exists_lift_of_isPullback h (w ≫ τ₁)
      (w ≫ τ₂) (map_comp_eq_of_app_eq a (by
        rw [ha, ha, hτ₁, hτ₂, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
          ← op_comp, hg₁']))
    let z : T'.unop ⟶ X' := Limits.pullback.lift w r (by ext1 <;> simp [hr₁, hr₂])
    have hz : z ≫ x' = w := Limits.pullback.lift_fst _ _ _
    refine ⟨⟨z⟩, ?_, congrArg ULift.up hz⟩
    apply Subtype.ext
    change (⟨z ≫ x' ≫ g⟩ : ULift.{u + 1} (T'.unop ⟶ V)) = ⟨w ≫ g⟩
    rw [← Category.assoc, hz]

include hD h in
/-- An fppf sheaf with a locally surjective map from a scheme whose kernel pair is represented
by `(t, s)`, with `t` locally of finite type, has representable diagonal. -/
theorem hasRepresentableDiagonal_of_isPullback (ht : LocallyOfFiniteType t.left) :
    HasRepresentableDiagonal Q.obj := by
  apply hasRepresentableDiagonal_of_representsEqualizer
  intro V x y
  let J : Sieve V := Presheaf.imageSieve a x ⊓ Presheaf.imageSieve a y
  have hJ : J ∈ fppfTopology S V :=
    (fppfTopology S).intersection_covering (Presheaf.imageSieve_mem (fppfTopology S) a x)
      (Presheaf.imageSieve_mem (fppfTopology S) a y)
  obtain ⟨X, ι, e, he⟩ := hD S (eqLocusSheaf Q x y) V (eqLocus x y).ι J hJ (by
    rintro T g ⟨⟨⟨τ₁⟩, hτ₁⟩, ⟨⟨τ₂⟩, hτ₂⟩⟩
    exact exists_isPullback_eqLocus a h ht x y g τ₁ τ₂ hτ₁ hτ₂)
  refine ⟨X, ι, ?_, fun T g ↦ ⟨?_, fun hg ↦ ?_⟩⟩
  · have : Mono ((schemeYoneda S).map ι) := by
      rw [← he]
      have hι : Mono (eqLocus x y).ι := inferInstance
      exact @mono_comp _ _ _ _ _ e.hom _ (eqLocus x y).ι hι
    exact mono_left_of_map_mono ι
  · rintro ⟨z, rfl⟩
    have h₁ := congrArg (fun φ ↦ φ.app (op T) ⟨z⟩) he
    have h₂ := (e.hom.app (op T) ⟨z⟩).2
    change (e.hom.app (op T) ⟨z⟩).1 = ⟨z ≫ ι⟩ at h₁
    rw [h₁] at h₂
    exact h₂
  · let w : (eqLocusSheaf Q x y).obj.obj (op T) := ⟨⟨g⟩, hg⟩
    refine ⟨(e.inv.app (op T) w).down, ?_⟩
    have h₁ := congrArg (fun φ ↦ φ.app (op T) (e.inv.app (op T) w)) he
    have h₂ : e.hom.app (op T) (e.inv.app (op T) w) = w := by simp
    change (e.hom.app (op T) (e.inv.app (op T) w)).1 = ⟨(e.inv.app (op T) w).down ≫ ι⟩ at h₁
    rw [h₂] at h₁
    exact (congrArg ULift.down h₁).symm

end Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPair
