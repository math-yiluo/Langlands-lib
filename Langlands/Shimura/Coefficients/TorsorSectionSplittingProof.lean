import Langlands.Shimura.Coefficients.TorsorSectionSplittingStatement
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

private lemma etale_prod_hom_ext {X T : Scheme.{u}} {A B : X.Etale}
    (a b : T ⟶ (A ⨯ B).left)
    (h₁ : a ≫ (prod.fst : A ⨯ B ⟶ A).left = b ≫ (prod.fst : A ⨯ B ⟶ A).left)
    (h₂ : a ≫ (prod.snd : A ⨯ B ⟶ B).left = b ≫ (prod.snd : A ⨯ B ⟶ B).left) : a = b := by
  have hb : b ≫ (A ⨯ B).hom = a ≫ (A ⨯ B).hom := by
    rw [← MorphismProperty.Over.w (prod.fst : A ⨯ B ⟶ A), ← Category.assoc, ← h₁, Category.assoc]
  let a' : Over.mk (a ≫ (A ⨯ B).hom) ⟶ (Scheme.Etale.forget X).obj (A ⨯ B) :=
    Over.homMk a
  let b' : Over.mk (a ≫ (A ⨯ B).hom) ⟶ (Scheme.Etale.forget X).obj (A ⨯ B) :=
    Over.homMk b hb
  have h : a' = b' := by
    apply BinaryFan.IsLimit.hom_ext
      (isLimitOfHasBinaryProductOfPreservesLimit (Scheme.Etale.forget X) A B)
    · exact Over.OverMorphism.ext h₁
    · exact Over.OverMorphism.ext h₂
  exact congrArg (fun f => f.left) h

private lemma torsor_graphs_cover {X : Scheme.{u}} {G : Type u} [Group G]
    (Y : Action X.Etale G) (hY : IsFiniteGeometricTorsor X Y) (U : Over Y.V) :
    Sieve.ofArrows (fun _ : G => U.left)
      (fun g => prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left)) ∈
        Scheme.smallEtaleTopology X (Y.V ⨯ U.left) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext z
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  let P := Y.V ⨯ U.left
  let Ω := SeparableClosure (P.left.residueField z)
  let p : Spec (.of Ω) ⟶ P.left :=
    (Scheme.SpecToEquivOfField Ω P.left).symm
      ⟨z, CommRingCat.ofHom (algebraMap (P.left.residueField z) Ω)⟩
  have hp : p default = z := by simp [p]
  let a := p ≫ (prod.snd : P ⟶ U.left).left ≫ U.hom.left
  let b := p ≫ (prod.fst : P ⟶ Y.V).left
  have hab : a ≫ Y.V.hom = b ≫ Y.V.hom := by
    simp [a, b, Category.assoc]
  obtain ⟨g, hg, _⟩ := hY.2.2.2 Ω a b hab
  let γ : U.left ⟶ P := prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left)
  have hγ₁ : γ.left ≫ (prod.fst : P ⟶ Y.V).left =
      U.hom.left ≫ (Y.ρ g).left :=
    congrArg (fun f : U.left ⟶ Y.V => f.left) (prod.lift_fst _ _)
  have hγ₂ : γ.left ≫ (prod.snd : P ⟶ U.left).left = 𝟙 _ :=
    congrArg (fun f : U.left ⟶ U.left => f.left) (prod.lift_snd _ _)
  have heq : p ≫ (prod.snd : P ⟶ U.left).left ≫ γ.left = p := by
    apply etale_prod_hom_ext
    · simpa only [Category.assoc, hγ₁] using
        (show p ≫ (prod.snd : P ⟶ U.left).left ≫ U.hom.left ≫ (Y.ρ g).left =
          p ≫ (prod.fst : P ⟶ Y.V).left by simpa only [a, b, Category.assoc] using hg)
    · simp only [Category.assoc, hγ₂, Category.comp_id]
  refine ⟨g, (p ≫ (prod.snd : P ⟶ U.left).left) default, ?_⟩
  change (p ≫ (prod.snd : P ⟶ U.left).left ≫ γ.left) default = z
  rw [heq, hp]

private lemma torsor_overlap_index_eq {X : Scheme.{u}} {G : Type u} [Group G]
    (Y : Action X.Etale G) (hY : IsFiniteGeometricTorsor X Y) (U : Over Y.V)
    {W : X.Etale} {g h : G} (f k : W ⟶ U.left)
    (heq : f ≫ prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left) =
      k ≫ prod.lift (U.hom ≫ Y.ρ h) (𝟙 U.left)) (z : W.left) : g = h := by
  have hfk : f = k := by
    simpa using congrArg (fun t => t ≫ prod.snd) heq
  subst k
  have hfst : f ≫ U.hom ≫ Y.ρ g = f ≫ U.hom ≫ Y.ρ h := by
    simpa using congrArg (fun t => t ≫ prod.fst) heq
  let Ω := SeparableClosure (W.left.residueField z)
  let p : Spec (.of Ω) ⟶ W.left :=
    (Scheme.SpecToEquivOfField Ω W.left).symm
      ⟨z, CommRingCat.ofHom (algebraMap (W.left.residueField z) Ω)⟩
  let a := p ≫ f.left ≫ U.hom.left
  have hgh : a ≫ (Y.ρ g).left = a ≫ (Y.ρ h).left := by
    have hh := congrArg (fun t : W ⟶ Y.V => p ≫ t.left) hfst
    change p ≫ (f.left ≫ U.hom.left ≫ (Y.ρ g).left) =
      p ≫ (f.left ≫ U.hom.left ≫ (Y.ρ h).left) at hh
    simpa only [a, Category.assoc] using hh
  have hab : a ≫ Y.V.hom = (a ≫ (Y.ρ g).left) ≫ Y.V.hom := by simp
  obtain ⟨t, _, ht⟩ := hY.2.2.2 Ω a (a ≫ (Y.ρ g).left) hab
  exact (ht g rfl).trans (ht h hgh.symm).symm

private instance module_forget_corepresentable (R : Type u) [CommRing R] :
    (forget (ModuleCat.{u} R)).IsCorepresentable :=
  (show (forget (ModuleCat.{u} R)).CorepresentableBy (ModuleCat.of R R) from
    { homEquiv := ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R R _).toEquiv
      homEquiv_comp := fun _ _ => rfl }).isCorepresentable

private lemma etale_sections_eq_of_empty {X : Scheme.{u}} {R : Type u} [CommRing R]
    (F : Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R))
    (W : X.Etale) [IsEmpty W.left] (s t : F.obj.obj (op W)) : s = t := by
  let P := F.obj ⋙ forget (ModuleCat.{u} R)
  have hP : Presieve.IsSheaf (Scheme.smallEtaleTopology X) P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (Scheme.smallEtaleTopology X) (forget (ModuleCat.{u} R))).obj F).property
  let f : ∀ i : Empty, (fun _ : Empty => W) i ⟶ W := fun i => nomatch i
  have hf : Sieve.ofArrows _ f ∈ Scheme.smallEtaleTopology X W := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext w
    exact isEmptyElim w
  apply (hP.isSheafFor _ hf).isSeparatedFor.ext
  rintro Z a ⟨i⟩
  exact i.elim

/-- The geometric torsor condition splits sections of every module sheaf along
its translated graphs. -/
theorem etaleTorsorSectionSplitting : EtaleTorsorSectionSplittingStatement.{u} := by
  intro X G _ Y hY R _ F U
  let P := F.obj ⋙ forget (ModuleCat.{u} R)
  have hP : Presieve.IsSheaf (Scheme.smallEtaleTopology X) P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (Scheme.smallEtaleTopology X) (forget (ModuleCat.{u} R))).obj F).property
  let γ : ∀ g : G, (fun _ : G => U.left) g ⟶ Y.V ⨯ U.left :=
    fun g => prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left)
  have hγ := hP.isSheafFor _ (torsor_graphs_cover Y hY U)
  rw [Function.bijective_iff_existsUnique]
  intro x
  have hx : Presieve.Arrows.Compatible P γ x := by
    intro g h W f k heq
    have hfk : f = k := by
      simpa [γ] using congrArg (fun t => t ≫ prod.snd) heq
    subst k
    by_cases hgh : g = h
    · subst h
      rfl
    · have : IsEmpty W.left := ⟨fun z => hgh (torsor_overlap_index_eq Y hY U f f heq z)⟩
      exact etale_sections_eq_of_empty F W _ _
  obtain ⟨s, hs, hu⟩ := (Presieve.isSheafFor_arrows_iff P γ).mp hγ x hx
  exact ⟨s, funext hs, fun t ht => hu t (fun g => congrFun ht g)⟩

end Langlands.Shimura.Coefficients
