import Langlands.Sheaf.Equivariant.NaturalActionSections

/-!
# The sheaf of invariant sections along a natural action

Let a group `K` act naturally along a functor `Φ : E ⥤ T`, and let `F` be a module presheaf
on `T` such that `Φ.op ⋙ F` is a sheaf on `E`, for instance a sheaf on `T` when `Φ` is
continuous. Then the presheaf of invariant sections `V ↦ F(Φ V)^K` is a sheaf on `E`: a
compatible family of invariant sections glues to a section of `F(Φ V)`, which is invariant
because its translates glue the same family. This rests on a general criterion: a presheaf
which is the joint equalizer of a family of endomorphisms of a sheaf is a sheaf.

For continuous `Φ`, this gives a left exact functor from module sheaves on `T` to module
sheaves on `E`. For a `G`-space `X`, it is the sheaf `(b_*F)^G` of the proof of
Berkovich's Theorem 1.4.2 (see `AnalyticInvariantSheaf`).
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite

universe v u vE uE vA uA uK uR w

section Equalizer

variable {E : Type uE} [Category.{vE} E] {A : Type uA} [Category.{vA} A]

/-- Let `ι : Q ⟶ P` be a componentwise monomorphism of presheaves into a sheaf `P`, and let
`e` be a family of endomorphisms of `P` fixing `ι`, such that every morphism into a value of
`P` fixed by all `e k` factors through `ι`. Then `Q` is a sheaf. -/
theorem isSheaf_of_isJointEqualizer {J : GrothendieckTopology E} {P Q : Eᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (ι : Q ⟶ P) [∀ V, Mono (ι.app V)] {I : Type*}
    (e : I → (P ⟶ P)) (he : ∀ k V, ι.app V ≫ (e k).app V = ι.app V)
    (hfac : ∀ (M : A) (V : Eᵒᵖ) (t : M ⟶ P.obj V), (∀ k, t ≫ (e k).app V = t) →
      ∃ t' : M ⟶ Q.obj V, t' ≫ ι.app V = t) :
    Presheaf.IsSheaf J Q := by
  intro M V S hS x hx
  let ιM := Functor.whiskerRight ι (coyoneda.obj (op M))
  have hsep := (hP M S hS).isSeparatedFor
  obtain ⟨t, ht, -⟩ := hP M S hS (x.map ιM) (hx.map ιM)
  have hinv : ∀ k, t ≫ (e k).app (op V) = t := fun k => by
    let eM := Functor.whiskerRight (e k) (coyoneda.obj (op M))
    refine hsep (x.map ιM) _ _ ?_ ht
    have h := ht.map eM
    have hx' : (x.map ιM).map eM = x.map ιM := by
      funext Y f hf
      change (x f hf ≫ ι.app _) ≫ (e k).app _ = x f hf ≫ ι.app _
      rw [Category.assoc, he]
    rwa [hx'] at h
  obtain ⟨t', ht'⟩ := hfac M (op V) t hinv
  refine ⟨t', fun Y f hf => ?_, fun t'' ht'' => ?_⟩
  · change t' ≫ Q.map f.op = x f hf
    rw [← cancel_mono (ι.app (op Y)), Category.assoc, ι.naturality, ← Category.assoc, ht']
    exact ht f hf
  · rw [← cancel_mono (ι.app (op V)), ht']
    exact hsep (x.map ιM) _ _ (ht''.map ιM) ht

end Equalizer

variable {T : Type u} [Category.{v} T] {E : Type uE} [Category.{vE} E]

namespace NaturalAction

variable {K : Type uK} [Group K] {Φ : E ⥤ T} (a : NaturalAction K Φ)
variable (R : Type uR) [CommRing R]

/-- The inclusion of the invariant sections into the sections over `Φ V`. -/
def invariantPresheafι (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : a.invariantPresheaf R F ⟶ Φ.op ⋙ F where
  app V := ModuleCat.ofHom (actionRepresentation F (a.act V.unop)).invariants.subtype
  naturality _ _ _ := rfl

@[simp]
theorem invariantPresheafι_app_apply (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (V : Eᵒᵖ)
    (s : (a.invariantPresheaf R F).obj V) :
    ((a.invariantPresheafι R F).app V).hom s = s.1 :=
  rfl

instance invariantPresheafι_mono (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (V : Eᵒᵖ) :
    Mono ((a.invariantPresheafι R F).app V) :=
  (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

/-- The action of `k` on the sections over the objects `Φ V`, as an endomorphism of the
presheaf `Φ.op ⋙ F`. -/
def sectionsEndo (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (k : K) : Φ.op ⋙ F ⟶ Φ.op ⋙ F where
  app V := F.map (a.act V.unop k).unop.op
  naturality V W f := by
    change F.map (Φ.map f.unop).op ≫ F.map (a.act W.unop k).unop.op =
      F.map (a.act V.unop k).unop.op ≫ F.map (Φ.map f.unop).op
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, a.comm]

@[simp]
theorem sectionsEndo_app (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (k : K) (V : Eᵒᵖ) :
    (a.sectionsEndo R F k).app V = F.map (a.act V.unop k).unop.op :=
  rfl

/-- If `Φ.op ⋙ F` is a sheaf, then the presheaf `V ↦ F(Φ V)^K` of invariant sections is a
sheaf. -/
theorem isSheaf_invariantPresheaf {J : GrothendieckTopology E} {F : Tᵒᵖ ⥤ ModuleCat.{w} R}
    (hF : Presheaf.IsSheaf J (Φ.op ⋙ F)) : Presheaf.IsSheaf J (a.invariantPresheaf R F) :=
  isSheaf_of_isJointEqualizer hF (a.invariantPresheafι R F) (a.sectionsEndo R F)
    (fun k V => by
      ext s
      exact s.2 k)
    (fun M V t ht =>
      ⟨ModuleCat.ofHom (LinearMap.codRestrict _ t.hom fun m k =>
          congrArg (fun φ => φ.hom m) (ht k)), rfl⟩)

variable (J : GrothendieckTopology T) (JE : GrothendieckTopology E) [Φ.IsContinuous JE J]

/-- For continuous `Φ`, the sheaf `V ↦ F(Φ V)^K` of invariant sections of a module sheaf
`F` on `T`, functorially in `F`. -/
def sheafInvariantSheafFunctor : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf JE (ModuleCat.{w} R) :=
  ObjectProperty.lift _ (a.sheafInvariantFunctor R J) fun F =>
    a.isSheaf_invariantPresheaf R (Φ.op_comp_isSheaf JE J F)

/-- The underlying presheaf of the sheaf of invariant sections. -/
def sheafInvariantSheafFunctorCompIso :
    a.sheafInvariantSheafFunctor R J JE ⋙ sheafToPresheaf JE (ModuleCat.{w} R) ≅
      a.sheafInvariantFunctor R J :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem sheafInvariantSheafFunctor_obj_obj (F : Sheaf J (ModuleCat.{w} R)) :
    ((a.sheafInvariantSheafFunctor R J JE).obj F).obj = a.invariantPresheaf R F.obj :=
  rfl

/-- The sheaf of invariant sections is left exact in the module sheaf. -/
instance sheafInvariantSheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (a.sheafInvariantSheafFunctor R J JE :
      Sheaf J (ModuleCat.{w} R) ⥤ Sheaf JE (ModuleCat.{w} R)) := by
  have : PreservesFiniteLimits (a.sheafInvariantSheafFunctor R J JE ⋙
      sheafToPresheaf JE (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso (a.sheafInvariantSheafFunctorCompIso R J JE).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf JE (ModuleCat.{w} R))

end NaturalAction

end Langlands.Sheaf.Equivariant
