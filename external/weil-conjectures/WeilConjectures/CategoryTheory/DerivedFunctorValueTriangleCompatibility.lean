/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion
import WeilConjectures.CategoryTheory.LeftDerivedValueMorphism
import WeilConjectures.CategoryTheory.DerivedFunctorShift
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- Retraction and common-stage factorization make the supplied cone a limit.
Source: Stacks Project, Categories, Definition 05PU(2). -/
private theorem valueCone_isLimit
    {J A : Type*} [Category J] [Category A] (G : J ⥤ A) (X : A)
    (u : (Functor.const J).obj X ⟶ G)
    (hu : ∃ j₀ : J, ∃ r : G.obj j₀ ⟶ X, u.app j₀ ≫ r = 𝟙 X ∧
      ∀ j : J, ∃ k : J, ∃ a : k ⟶ j₀, ∃ b : k ⟶ j,
        G.map b = G.map a ≫ r ≫ u.app j) : Nonempty (IsLimit (Cone.mk X u)) := by
  obtain ⟨j₀, r, hr, hfactor⟩ := hu
  exact ⟨{
    lift := fun v ↦ v.π.app j₀ ≫ r
    fac := by
      intro v j
      obtain ⟨k, a, b, hab⟩ := hfactor j
      calc
        (v.π.app j₀ ≫ r) ≫ u.app j =
            (v.π.app k ≫ G.map a) ≫ r ≫ u.app j := by rw [v.w a, Category.assoc]
        _ = v.π.app k ≫ G.map b := by rw [Category.assoc, ← hab]
        _ = v.π.app j := v.w b
    uniq := by
      intro v m hm
      calc
        m = m ≫ (u.app j₀ ≫ r) := by rw [hr, Category.comp_id]
        _ = v.π.app j₀ ≫ r := by rw [← Category.assoc, hm j₀] }⟩

/-- A compatible third derived map can be chosen together with distinguishedness.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause (dual argument).

Proof: Complete lf by TR1 to (LX, LY, K, lf, b, c). Keep a retracting
stage sY of the supplied second cone. MS2 gives a lift f₁ of T.mor₁ into sY.
The common-stage clause of the first cone gives maps a and t with
F(t) = F(a) alpha₀ uX(s₁). Put f' = t f₁ and alpha = F(a) alpha₀.
Naturality proves uX(s) alpha = identity, and hf with the second retraction proves
F(f') beta = alpha lf. Complete f' by TR1, extend the denominators using MS6,
and extend alpha and beta using TR3, retaining both remaining squares of q.
Apply leftDerived_triangle_retraction_homColimit to this concrete comparison.
The pro criterion 05PY constructs the cone uK with the third component gamma
as a retraction. Its identity-class equations, interpreted at a common stage
of the filtered Hom-colimit, give the factorization certificate for this same uK.
Use 05SA to obtain the derived second map into K. Its equation at the concrete
stage, composed with gamma, identifies it with b by the retained second square.
For the third map, 05SU gives a value V at T.obj₁[1] and the canonical comparison
LX[1] to V for its supplied cone. Apply 05SA to T.mor₃ and transport the result
back to LX[1]. This gives all shifted denominator-square equations. At the
concrete comparison stage, compose with commShiftIso.hom and shift(alpha).
The retraction uX(s) alpha = identity and q's third square identify this map
with c. Thus c satisfies every required shifted cone equation.
The private helper proves directly that a retraction-certified cone is a limit:
its lift of another cone v is v(s₀) r; common-stage factorization proves the leg
equations and u(s₀) r = identity proves uniqueness. Apply limit uniqueness to
uK and the supplied uZ to get e : K to LZ preserving all legs. A fraction square
for T.mor₂ with a retracting target leg then proves b e.hom = lg.
Set lh = e.inv c. Transport the distinguished completion along identities at
LX and LY and e at K. Compose the established third cone equation with e.inv
to obtain the required equation for every supplied h'.
(blueprint: lem-pur-derived-functor-triangles-05sc-value-triangle-compatibility) -/
theorem leftDerived_value_triangle_extension_compat
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (LX LY LZ : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
        (f' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₁ = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
        (g' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₂ = g' ≫ s'.hom →
          uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    : ∃ lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX,
        Triangle.mk lf lg lh ∈ distTriang D ∧
        (∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
          (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left),
          s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom →
            uZ.app s ≫ F.map h' =
              lh ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
                (F.commShiftIso (1 : ℤ)).inv.app s'.left) := by
  classical
  have : S.HasRightCalculusOfFractions := hS.1.1.2
  have : S.IsCompatibleWithTriangulation := hS.2
  obtain ⟨K, b, c, hK⟩ := distinguished_cocone_triangle lf
  -- First make the retractions commute with the first arrow.
  have huX' := huX
  have huY' := huY
  obtain ⟨sY, β, hβ, _⟩ := huY
  obtain ⟨sX, α₀, hα₀, hfactor⟩ := huX
  obtain ⟨d, hd⟩ :=
    (MorphismProperty.LeftFraction.mk T.mor₁ sY.hom sY.prop).exists_rightFraction
  let s₁ : S.Over ⊤ T.obj₁ := MorphismProperty.Over.mk ⊤ d.s d.hs
  obtain ⟨s, a, t, ht⟩ := hfactor s₁
  let f' : s.left ⟶ sY.left := t.left ≫ d.f
  let α : F.obj s.left ⟶ LX := F.map a.left ≫ α₀
  have hα : uX.app s ≫ α = 𝟙 LX := by
    have hn : uX.app s ≫ F.map a.left = uX.app sX := by
      simpa using (uX.naturality a).symm
    dsimp [α]
    rw [← Category.assoc, hn, hα₀]
  have hsq : s.hom ≫ T.mor₁ = f' ≫ sY.hom := by
    calc
      s.hom ≫ T.mor₁ = (t.left ≫ d.s) ≫ T.mor₁ := by
        rw [show t.left ≫ d.s = s.hom from MorphismProperty.Over.w t]
      _ = f' ≫ sY.hom := by dsimp [f']; rw [Category.assoc, hd, Category.assoc]
  have hαβ : F.map f' ≫ β = α ≫ lf := by
    calc
      F.map f' ≫ β = F.map t.left ≫ F.map d.f ≫ β := by
        dsimp [f']; rw [F.map_comp, Category.assoc]
      _ = F.map a.left ≫ α₀ ≫ uX.app s₁ ≫ F.map d.f ≫ β := by
        rw [ht, Category.assoc, Category.assoc]
      _ = α ≫ lf := by
        have h := congrArg (fun m ↦ F.map a.left ≫ α₀ ≫ m ≫ β) (hf s₁ sY d.f hd)
        simpa only [Category.assoc, hβ, Category.comp_id, α] using h
  -- TR1, MS6, and TR3 produce the concrete comparison required by the cone lemma.
  obtain ⟨Z', g', h', hU⟩ := distinguished_cocone_triangle f'
  let U := Triangle.mk f' g' h'
  obtain ⟨z, hz, hz₂, hz₃⟩ :=
    MorphismProperty.compatible_with_triangulation (W := S) U T hU hT
      s.hom sY.hom s.prop sY.prop hsq.symm
  let p : U ⟶ T := Triangle.homMk _ _ s.hom sY.hom z hsq.symm hz₂ hz₃
  obtain ⟨γ, hγ₂, hγ₃⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj U) (Triangle.mk lf b c) (F.map_distinguished U hU) hK
    α β hαβ
  let q : F.mapTriangle.obj U ⟶ Triangle.mk lf b c :=
    Triangle.homMk _ _ α β γ hαβ hγ₂ hγ₃
  let sK : S.Over ⊤ T.obj₃ := MorphismProperty.Over.mk ⊤ p.hom₃ hz
  let G := MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F
  have : IsCofiltered (S.Over ⊤ T.obj₃) := hZ.1
  have hbij := leftDerived_triangle_retraction_homColimit F S hS T hT LX LY
    hX hY uX uY huX' huY' lf K b c hK U hU p s.prop sY.prop hz q hα hβ
  obtain ⟨hvalK, uK, hrK, hlegs⟩ :=
    homColimit_essentiallyConstantProDiagram G K sK γ hbij
  have huK : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ K,
      uK.app s₀ ≫ r = 𝟙 K ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uK.app s := by
    refine ⟨sK, γ, hrK, ?_⟩
    intro j
    obtain ⟨k, a, b, heq⟩ :=
      ((G.op ⋙ yoneda.obj (G.obj j)).ιColimitType_eq_iff_of_isFiltered
        (j := Opposite.op sK) (j' := Opposite.op j) (γ ≫ uK.app j) (𝟙 (G.obj j))).mp (hlegs j)
    refine ⟨k.unop, a.unop, b.unop, ?_⟩
    change G.map a.unop ≫ (γ ≫ uK.app j) = G.map b.unop ≫ 𝟙 (G.obj j) at heq
    change G.map b.unop = G.map a.unop ≫ γ ≫ uK.app j
    simpa only [Category.comp_id] using heq.symm
  -- Identify the second map by its equation at the concrete comparison stage.
  obtain ⟨lb, hlb, _⟩ := leftDerived_value_morphism F S hS T.mor₂ LY K
    hY hvalK uY uK huY' huK
  have hlb_eq : lb = b := by
    have hsq₂ : sY.hom ≫ T.mor₂ = U.mor₂ ≫ sK.hom := hz₂.symm
    have hlb_stage := (hlb sY sK U.mor₂ hsq₂).1
    calc
      lb = (lb ≫ uK.app sK) ≫ γ := by
        rw [Category.assoc, hrK, Category.comp_id]
      _ = (uY.app sY ≫ F.map U.mor₂) ≫ γ := by rw [hlb_stage]
      _ = b := by
        rw [Category.assoc]
        change uY.app sY ≫ (F.map g' ≫ γ) = b
        have hsecond : F.map g' ≫ γ = β ≫ b := hγ₂
        rw [hsecond]
        rw [← Category.assoc, hβ]
        change 𝟙 LY ≫ b = b
        exact Category.id_comp b
  have hb (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
      (g' : s.left ⟶ s'.left) (hsq : s.hom ≫ T.mor₂ = g' ≫ s'.hom) :
      uY.app s ≫ F.map g' = b ≫ uK.app s' := by
    simpa only [hlb_eq] using (hlb s s' g' hsq).1
  -- Use a genuine shifted value and its canonical comparison to identify c.
  have hshift := isTriangulatedLeftDerivedDefinedAt_shift_iff F S hS T.obj₁ (1 : ℤ)
  obtain ⟨V, hV⟩ := hshift.1.mp ⟨LX, hX⟩
  have hV' := hV
  obtain ⟨_, uV, sV, rV, hrV, hfacV⟩ := hV'
  have huV : ∃ s₀ : S.Over ⊤ ((shiftFunctor C (1 : ℤ)).obj T.obj₁),
      ∃ r : F.obj s₀.left ⟶ V, uV.app s₀ ≫ r = 𝟙 V ∧
        ∀ s : S.Over ⊤ ((shiftFunctor C (1 : ℤ)).obj T.obj₁),
          ∃ t : S.Over ⊤ ((shiftFunctor C (1 : ℤ)).obj T.obj₁),
            ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
              F.map b.left = F.map a.left ≫ r ≫ uV.app s :=
    ⟨sV, rV, hrV, hfacV⟩
  obtain ⟨hlimX⟩ := valueCone_isLimit _ LX uX huX'
  obtain ⟨hlimV⟩ := valueCone_isLimit _ V uV huV
  obtain ⟨eV, heV, _⟩ :=
    hshift.2 ⟨LX, hX⟩ LX V hX hV uX uV ⟨hlimX⟩ ⟨hlimV⟩
  obtain ⟨lc₀, hlc₀, _⟩ := leftDerived_value_morphism F S hS T.mor₃ K V
    hvalK hV uK uV huK huV
  let lc := lc₀ ≫ eV.inv
  have hlc (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
      (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left)
      (hsq : s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom) :
      uK.app s ≫ F.map h' =
        lc ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
          (F.commShiftIso (1 : ℤ)).inv.app s'.left := by
    let sShift : S.Over ⊤ ((shiftFunctor C (1 : ℤ)).obj T.obj₁) :=
      MorphismProperty.Over.mk ⊤ ((shiftFunctor C (1 : ℤ)).map s'.hom)
        (S.shift s'.prop (1 : ℤ))
    have hsShift := heV s' (S.shift s'.prop (1 : ℤ))
    have hleg : uV.app sShift = eV.inv ≫
        (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
          (F.commShiftIso (1 : ℤ)).inv.app s'.left := by
      rw [← hsShift]
      simp only [Iso.inv_hom_id_assoc]
      rfl
    rw [(hlc₀ s sShift h' hsq).1, hleg]
    simp only [lc, Category.assoc]
  have hlc_eq : lc = c := by
    have hs₃ : sK.hom ≫ T.mor₃ = U.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map s.hom :=
      hz₃.symm
    have hstage := hlc sK s U.mor₃ hs₃
    have hstage' := congrArg
      (fun m ↦ m ≫ (F.commShiftIso (1 : ℤ)).hom.app s.left ≫
        (shiftFunctor D (1 : ℤ)).map α) hstage
    have hc_stage : uK.app sK ≫ F.map U.mor₃ ≫
        (F.commShiftIso (1 : ℤ)).hom.app s.left ≫
          (shiftFunctor D (1 : ℤ)).map α = lc := by
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
        hα, Functor.map_id, Category.comp_id] using hstage'
    rw [← hc_stage]
    have hthird : (F.map U.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app s.left) ≫
        (shiftFunctor D (1 : ℤ)).map α = γ ≫ c := hγ₃
    rw [← Category.assoc (F.map U.mor₃), hthird, ← Category.assoc, hrK]
    change 𝟙 K ≫ c = c
    exact Category.id_comp c
  have hc (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
      (h' : s.left ⟶ (shiftFunctor C (1 : ℤ)).obj s'.left)
      (hsq : s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor C (1 : ℤ)).map s'.hom) :
      uK.app s ≫ F.map h' = c ≫ (shiftFunctor D (1 : ℤ)).map (uX.app s') ≫
        (F.commShiftIso (1 : ℤ)).inv.app s'.left := by
    simpa only [hlc_eq] using hlc s s' h' hsq
  -- The two certified cones at Z are limits of exactly the same diagram.
  obtain ⟨hlimK⟩ := valueCone_isLimit G K uK huK
  obtain ⟨hlimZ⟩ := valueCone_isLimit G LZ uZ huZ
  let e : K ≅ LZ := hlimK.conePointUniqueUpToIso hlimZ
  have he (s : S.Over ⊤ T.obj₃) : e.hom ≫ uZ.app s = uK.app s :=
    hlimK.conePointUniqueUpToIso_hom_comp hlimZ s
  -- A fraction square with a retracting target leg identifies the supplied lg.
  obtain ⟨sZ, rZ, hrZ, _⟩ := huZ
  obtain ⟨d₂, hd₂⟩ :=
    (MorphismProperty.LeftFraction.mk T.mor₂ sZ.hom sZ.prop).exists_rightFraction
  let s₂ : S.Over ⊤ T.obj₂ := MorphismProperty.Over.mk ⊤ d₂.s d₂.hs
  have hbe : b ≫ e.hom = lg := by
    have heq : (b ≫ e.hom) ≫ uZ.app sZ = lg ≫ uZ.app sZ := by
      rw [Category.assoc, he, ← hb s₂ sZ d₂.f hd₂, hg s₂ sZ d₂.f hd₂]
    calc
      b ≫ e.hom = ((b ≫ e.hom) ≫ uZ.app sZ) ≫ rZ := by
        rw [Category.assoc, hrZ, Category.comp_id]
      _ = (lg ≫ uZ.app sZ) ≫ rZ := by rw [heq]
      _ = lg := by rw [Category.assoc, hrZ, Category.comp_id]
  let lh := e.inv ≫ c
  refine ⟨lh, ?_, ?_⟩
  · let et : Triangle.mk lf b c ≅ Triangle.mk lf lg lh :=
      Triangle.isoMk _ _ (Iso.refl LX) (Iso.refl LY) e
        (by
          change lf ≫ 𝟙 LY = 𝟙 LX ≫ lf
          rw [Category.comp_id, Category.id_comp])
        (by
          change b ≫ e.hom = 𝟙 LY ≫ lg
          rw [Category.id_comp]
          exact hbe)
        (by
          change c ≫ (shiftFunctor D (1 : ℤ)).map (𝟙 LX) = e.hom ≫ (e.inv ≫ c)
          rw [Functor.map_id, Category.comp_id, Iso.hom_inv_id_assoc])
    exact (distinguished_iff_of_iso et).mp hK
  · intro s s' h' hsq
    have hei : e.inv ≫ uK.app s = uZ.app s := by rw [← he]; simp
    rw [← hei, Category.assoc, hc s s' h' hsq]
    simp only [lh, Category.assoc]


end CategoryTheory.Functor
