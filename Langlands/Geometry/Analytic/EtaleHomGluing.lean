import Langlands.Geometry.Analytic.EtaleSite

/-! # Conditional étale gluing of analytic morphisms -/

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- If the Hom presheaf is a sheaf, equality of complete analytic morphisms
can be checked after an étale source lift through every source point. -/
theorem hom_ext_of_etale_local_eq
    {X T : LocalizedCategory.{u, v, v} (K := K)}
    (hSheaf : Presieve.IsSheaf (etaleTopology X) ((MorphismProperty.Over.forget _ _ X ⋙ Over.forget X).op ⋙ yoneda.obj T))
    (f g : X ⟶ T)
    (hlocal : ∀ x : localizedSpaceFunctor.obj X,
      ∃ (U : LocalizedCategory.{u, v, v} (K := K)) (e : U ⟶ X),
        etale e ∧ x ∈ Set.range (localizedSpaceFunctor.map e) ∧ e ≫ f = e ≫ g) :
    f = g := by
  let B : EtaleSite X :=
    MorphismProperty.Over.mk ⊤ (𝟙 X) (etale_of_isIso _)
  let S : Sieve B :=
    { arrows := fun _ e => e.left ≫ f = e.left ≫ g
      downward_closed := by
        intro U V e he a
        exact (Category.assoc a.left (show U.left ⟶ X from e.left) f).trans
          ((congrArg (fun k : U.left ⟶ T => a.left ≫ k) he).trans
            (Category.assoc a.left (show U.left ⟶ X from e.left) g).symm) }
  have hS : S ∈ etaleTopology X B := by
    apply mem_etaleTopology_of_jointlySurjective
    intro x
    obtain ⟨U, e, he, hx, heq⟩ := hlocal x
    let V : EtaleSite X := MorphismProperty.Over.mk ⊤ e he
    let a : V ⟶ B := MorphismProperty.Over.homMk e (Category.comp_id e)
    exact ⟨V, a, heq, hx⟩
  exact (hSheaf S hS).isSeparatedFor.ext (fun _ _ he => he)


/-- Local lifts through a jointly monic pair glue if the three relevant
analytic Hom presheaves are sheaves. No categorical pullbacks are assumed. -/
theorem exists_hom_of_etale_local_lifts
    {P X Y S : LocalizedCategory.{u, v, v} (K := K)}
    (fst : P ⟶ X) (snd : P ⟶ Y) (a : S ⟶ X) (b : S ⟶ Y)
    (hP : Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj P))
    (hX : Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj X))
    (hY : Presieve.IsSheaf (etaleTopology S)
      ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj Y))
    (hmono : ∀ (U : LocalizedCategory.{u, v, v} (K := K)) (l m : U ⟶ P),
      l ≫ fst = m ≫ fst → l ≫ snd = m ≫ snd → l = m)
    (hlocal : ∀ s : localizedSpaceFunctor.obj S,
      ∃ (U : LocalizedCategory.{u, v, v} (K := K)) (e : U ⟶ S),
        etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
          ∃ l : U ⟶ P, l ≫ fst = e ≫ a ∧ l ≫ snd = e ≫ b) :
    ∃ l : S ⟶ P, l ≫ fst = a ∧ l ≫ snd = b := by
  classical
  let F : (EtaleSite S)ᵒᵖ ⥤ Type _ :=
    (MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj P
  let B : EtaleSite S :=
    MorphismProperty.Over.mk ⊤ (𝟙 S) (etale_of_isIso _)
  let R : Sieve B :=
    { arrows := fun U _ => ∃ l : U.left ⟶ P,
        l ≫ fst = U.hom ≫ a ∧ l ≫ snd = U.hom ≫ b
      downward_closed := by
        intro U V e he r
        obtain ⟨l, hl₁, hl₂⟩ := he
        refine ⟨r.left ≫ l, ?_, ?_⟩
        · rw [Category.assoc, hl₁, ← Category.assoc, MorphismProperty.Over.w]
        · rw [Category.assoc, hl₂, ← Category.assoc, MorphismProperty.Over.w] }
  have hR : R ∈ etaleTopology S B := by
    apply mem_etaleTopology_of_jointlySurjective
    intro s
    obtain ⟨U, e, he, hs, l, hl₁, hl₂⟩ := hlocal s
    let V : EtaleSite S := MorphismProperty.Over.mk ⊤ e he
    let r : V ⟶ B := MorphismProperty.Over.homMk e (Category.comp_id e)
    exact ⟨V, r, ⟨l, hl₁, hl₂⟩, hs⟩
  let x : Presieve.FamilyOfElements F R.arrows := fun _ _ he => Classical.choose he
  have hx₁ {U : EtaleSite S} (e : U ⟶ B) (he : R e) :
      x e he ≫ fst = U.hom ≫ a := (Classical.choose_spec he).1
  have hx₂ {U : EtaleSite S} (e : U ⟶ B) (he : R e) :
      x e he ≫ snd = U.hom ≫ b := (Classical.choose_spec he).2
  have hx₁' {U V : EtaleSite S} (e : U ⟶ B) (he : R e) (r : V ⟶ U) :
      (r.left ≫ x e he) ≫ fst = V.hom ≫ a :=
    (Category.assoc r.left (x e he) fst).trans
      ((congrArg (fun k : U.left ⟶ X => r.left ≫ k) (hx₁ e he)).trans
        ((Category.assoc r.left U.hom a).symm.trans
          (congrArg (fun k : V.left ⟶ S => k ≫ a) (MorphismProperty.Over.w r))))
  have hx₂' {U V : EtaleSite S} (e : U ⟶ B) (he : R e) (r : V ⟶ U) :
      (r.left ≫ x e he) ≫ snd = V.hom ≫ b :=
    (Category.assoc r.left (x e he) snd).trans
      ((congrArg (fun k : U.left ⟶ Y => r.left ≫ k) (hx₂ e he)).trans
        ((Category.assoc r.left U.hom b).symm.trans
          (congrArg (fun k : V.left ⟶ S => k ≫ b) (MorphismProperty.Over.w r))))
  have hx : x.Compatible := by
    intro U₁ U₂ U g₁ g₂ e₁ e₂ he₁ he₂ _
    change g₁.left ≫ x e₁ he₁ = g₂.left ≫ x e₂ he₂
    apply hmono U.left
    · exact (hx₁' e₁ he₁ g₁).trans (hx₁' e₂ he₂ g₂).symm
    · exact (hx₂' e₁ he₁ g₁).trans (hx₂' e₂ he₂ g₂).symm
  let l : S ⟶ P := (hP R hR).amalgamate x hx
  have hl {U : EtaleSite S} (e : U ⟶ B) (he : R e) :
      (show U.left ⟶ S from e.left) ≫ l = x e he :=
    (hP R hR).valid_glue hx e he
  have heq {U : EtaleSite S} (e : U ⟶ B) :
      (show U.left ⟶ S from e.left) = U.hom :=
    (Category.comp_id (show U.left ⟶ S from e.left)).symm.trans
      (MorphismProperty.Over.w e)
  refine ⟨l, ?_, ?_⟩
  · apply (hX R hR).isSeparatedFor.ext
    intro U e he
    change (show U.left ⟶ S from e.left) ≫ (l ≫ fst) =
      (show U.left ⟶ S from e.left) ≫ a
    exact (Category.assoc (show U.left ⟶ S from e.left) l fst).symm.trans
      ((congrArg (fun k : U.left ⟶ P => k ≫ fst) (hl e he)).trans
        ((hx₁ e he).trans (congrArg (fun k : U.left ⟶ S => k ≫ a) (heq e).symm)))
  · apply (hY R hR).isSeparatedFor.ext
    intro U e he
    change (show U.left ⟶ S from e.left) ≫ (l ≫ snd) =
      (show U.left ⟶ S from e.left) ≫ b
    exact (Category.assoc (show U.left ⟶ S from e.left) l snd).symm.trans
      ((congrArg (fun k : U.left ⟶ P => k ≫ snd) (hl e he)).trans
        ((hx₂ e he).trans (congrArg (fun k : U.left ⟶ S => k ≫ b) (heq e).symm)))

/-- A commuting square is a pullback if its projections are jointly monic
and all compatible cones admit lifts étale-locally at each source point,
assuming the relevant Hom-sheaf properties. -/
theorem isPullback_of_etale_local_lifts
    {P X Y Z : LocalizedCategory.{u, v, v} (K := K)}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hw : fst ≫ f = snd ≫ g)
    (hSheaf : ∀ (S T : LocalizedCategory.{u, v, v} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj T))
    (hmono : ∀ (S : LocalizedCategory.{u, v, v} (K := K)) (l m : S ⟶ P),
      l ≫ fst = m ≫ fst → l ≫ snd = m ≫ snd → l = m)
    (hlocal : ∀ (S : LocalizedCategory.{u, v, v} (K := K))
      (a : S ⟶ X) (b : S ⟶ Y), a ≫ f = b ≫ g →
      ∀ s : localizedSpaceFunctor.obj S,
        ∃ (U : LocalizedCategory.{u, v, v} (K := K)) (e : U ⟶ S),
          etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
            ∃ l : U ⟶ P, l ≫ fst = e ≫ a ∧ l ≫ snd = e ≫ b) :
    IsPullback fst snd f g := by
  classical
  have hl (c : Limits.PullbackCone f g) :
      ∃ l : c.pt ⟶ P, l ≫ fst = c.fst ∧ l ≫ snd = c.snd :=
    exists_hom_of_etale_local_lifts fst snd c.fst c.snd
      (hSheaf _ _) (hSheaf _ _) (hSheaf _ _) hmono
      (hlocal c.pt c.fst c.snd c.condition)
  exact IsPullback.of_isLimit (Limits.PullbackCone.IsLimit.mk hw
    (fun c => Classical.choose (hl c))
    (fun c => (Classical.choose_spec (hl c)).1)
    (fun c => (Classical.choose_spec (hl c)).2)
    (fun c m hm₁ hm₂ => hmono c.pt m _
      (hm₁.trans (Classical.choose_spec (hl c)).1.symm)
      (hm₂.trans (Classical.choose_spec (hl c)).2.symm)))

end Langlands.Analytic.SaturatedAtlasPresentation
