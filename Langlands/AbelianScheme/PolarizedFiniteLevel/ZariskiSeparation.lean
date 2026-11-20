import Langlands.AbelianScheme.PolarizedFiniteLevel.Functor
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseZariski
import Langlands.GroupScheme.Descent.EtaleCoverHomDescent
import Langlands.GroupScheme.Descent.DatumRelation

/-! # Zariski separation of ordinary polarized full-level data under rigidity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

/-! ### Open covers as étale covering families -/

section Cover

variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)

/-- A covering family of opens, as a small étale covering family. -/
def etaleCoverOfOpens : Scheme.Cover.{u} (Scheme.precoverage @Etale) X :=
  (X.openCoverOfIsOpenCover U hU).changeProp (fun i => (inferInstance : Etale (U i).ι))

include hU in
/-- Homomorphisms of abelian schemes are determined by their restrictions to a covering
family of opens. -/
theorem hom_ext_of_opens {A B : AbelianScheme X} {f f' : A ⟶ B}
    (h : ∀ i, (AbelianScheme.baseChange (U i).ι).map f =
      (AbelianScheme.baseChange (U i).ι).map f') : f = f' := by
  have h' := GroupScheme.Descent.EtaleCoverHomDescent.groupHom_ext (etaleCoverOfOpens U hU)
    (b := AbelianScheme.groupHom f) (c := AbelianScheme.groupHom f')
    (fun i => congrArg Additive.toMul (h i))
  exact Additive.toMul.injective h'

include hU in
/-- Ordered torsion sections are determined by their restrictions to a covering family
of opens. -/
theorem pullbackTuple_injective_of_opens {A : AbelianScheme X} {g n : ℕ}
    {v w : SectionTuple A g n} (h : ∀ i, pullbackTuple (U i).ι v = pullbackTuple (U i).ι w) :
    v = w := by
  funext k
  apply toSection_injective A.toGrp (Over.mk (𝟙 X)) n
  change Additive.ofMul (Additive.toMul (v k)).val = Additive.ofMul (Additive.toMul (w k)).val
  congr 1
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover U hU)
  intro i
  change (U i).ι ≫ (Additive.toMul (v k)).val.left = (U i).ι ≫ (Additive.toMul (w k)).val.left
  rw [← pullbackTuple_fst, ← pullbackTuple_fst, h i]

end Cover

/-! ### Gluing isomorphisms of abelian schemes -/

section GlueIso

variable {S : Scheme.{u}}

/-- The isomorphism of underlying group schemes of an isomorphism of abelian schemes. -/
def grpIso {A B : AbelianScheme S} (e : A ≅ B) : A.toGrp ≅ B.toGrp where
  hom := AbelianScheme.groupHom e.hom
  inv := AbelianScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

/-- An isomorphism of abelian schemes from one of their underlying group schemes. -/
def ofGrpIso {A B : AbelianScheme S} (e : A.toGrp ≅ B.toGrp) : A ≅ B where
  hom := Additive.ofMul e.hom
  inv := Additive.ofMul e.inv
  hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
  inv_hom_id := congrArg Additive.ofMul e.inv_hom_id

end GlueIso

/-! ### Restriction of polarized isomorphisms and rigidity -/

section Restrict

variable {P : Prerequisites.{u}} {g d n : ℕ}

/-- Restrict a polarized isomorphism between pullbacks along `f` further along `q`, with
the direct pullbacks along `q ≫ f` as endpoints. -/
def PolarizedIso.restrict {S T V : Scheme.{u}} {a b : Datum P S g d n} {f : T ⟶ S}
    (e : PolarizedIso (a.pullback f) (b.pullback f)) (q : V ⟶ T) :
    PolarizedIso (a.pullback (q ≫ f)) (b.pullback (q ≫ f)) :=
  (a.pullbackCompIso f q).trans ((e.pullback q).trans (b.pullbackCompIso f q).symm)

/-- The underlying group homomorphism of a restriction is the Library's pulled morphism. -/
theorem PolarizedIso.groupHom_restrict {S T V : Scheme.{u}} {a b : Datum P S g d n}
    {f : T ⟶ S} (e : PolarizedIso (a.pullback f) (b.pullback f)) (q : V ⟶ T) :
    AbelianScheme.groupHom (e.restrict q).abelianIso.hom =
      GroupScheme.Descent.pullHom q rfl rfl (AbelianScheme.groupHom e.abelianIso.hom) := by
  simp [GroupScheme.Descent.pullHom, GroupScheme.Descent.pullbackComparison,
    PolarizedIso.restrict]
  rfl

/-- Evaluate a restricted polarized isomorphism on a test point. -/
theorem PolarizedIso.restrict_eval {S T V Z : Scheme.{u}} {a b : Datum P S g d n}
    {f : T ⟶ S} (e : PolarizedIso (a.pullback f) (b.pullback f)) (q : V ⟶ T)
    (x : Z ⟶ a.abelian.X.left) (z : Z ⟶ V) (hx : x ≫ a.abelian.X.hom = z ≫ q ≫ f) :
    pullback.lift x z hx ≫ AbelianScheme.hom (e.restrict q).abelianIso.hom ≫
        pullback.fst b.abelian.X.hom (q ≫ f) =
      pullback.lift x (z ≫ q) (by rw [Category.assoc]; exact hx) ≫
        AbelianScheme.hom e.abelianIso.hom ≫ pullback.fst b.abelian.X.hom f := by
  have h := GroupScheme.Descent.pullHom_eval q (rfl : q ≫ f = q ≫ f) rfl
    (AbelianScheme.groupHom e.abelianIso.hom) x z hx
  rw [← e.groupHom_restrict q] at h
  exact h

/-- If every polarized automorphism of `b` is the identity, then any two polarized
isomorphisms `a ≅ b` coincide. -/
theorem PolarizedIso.eq_of_rigid {S : Scheme.{u}} {a b : Datum P S g d n}
    (hb : ∀ α : PolarizedIso b b, α = PolarizedIso.refl b) (α β : PolarizedIso a b) :
    α = β := by
  have h : α.abelianIso.inv ≫ β.abelianIso.hom = 𝟙 _ :=
    congrArg (fun c0 : PolarizedIso b b => c0.abelianIso.hom) (hb (α.symm.trans β))
  have hab : α.abelianIso = β.abelianIso := by
    ext1
    calc α.abelianIso.hom = α.abelianIso.hom ≫ α.abelianIso.inv ≫ β.abelianIso.hom := by
          rw [h, Category.comp_id]
      _ = β.abelianIso.hom := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  cases α
  cases β
  cases hab
  rfl

/-- Under rigidity, polarized isomorphisms over equal base maps have equal values on
every test point. -/
theorem PolarizedIso.eval_eq_of_rigid {S T Z : Scheme.{u}} {a b : Datum P S g d n}
    {c c' : T ⟶ S} (hc : c = c')
    (hb : ∀ α : PolarizedIso (b.pullback c') (b.pullback c'), α = PolarizedIso.refl _)
    (E : PolarizedIso (a.pullback c) (b.pullback c))
    (E' : PolarizedIso (a.pullback c') (b.pullback c'))
    (x : Z ⟶ a.abelian.X.left) (z : Z ⟶ T) (hx : x ≫ a.abelian.X.hom = z ≫ c)
    (hx' : x ≫ a.abelian.X.hom = z ≫ c') :
    pullback.lift x z hx ≫ AbelianScheme.hom E.abelianIso.hom ≫
        pullback.fst b.abelian.X.hom c =
      pullback.lift x z hx' ≫ AbelianScheme.hom E'.abelianIso.hom ≫
        pullback.fst b.abelian.X.hom c' := by
  subst hc
  rw [PolarizedIso.eq_of_rigid hb E E']

end Restrict

/-! ### Separation under rigidity -/

section Separation

variable {P : Prerequisites.{0}} {g d n : ℕ}

/-- The source of an open immersion into a level base, as a level base. -/
def levelBaseOfOpenImmersion (S : LevelBase n) {T : Scheme.{0}} (f : T ⟶ S.obj)
    [IsOpenImmersion f] : LevelBase n :=
  haveI := isLocallyNoetherian_of_isOpenImmersion f
  LevelBase.ofScheme T (by simpa only [map_natCast] using S.level_isUnit.map f.appTop.hom)

/-- Under rigidity, local polarized isomorphisms on two members of an open cover take the
same value on every pair of test points with the same image in the source abelian scheme. -/
theorem eval_compatible_of_rigid
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (a b : Datum P S.obj g d n)
    (e : ∀ i, PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι))
    {Z : Scheme.{0}} (i j : I) (x : Z ⟶ pullback a.abelian.X.hom (U i).ι)
    (y : Z ⟶ pullback a.abelian.X.hom (U j).ι)
    (hxy : x ≫ pullback.fst a.abelian.X.hom (U i).ι = y ≫ pullback.fst a.abelian.X.hom (U j).ι) :
    x ≫ AbelianScheme.hom (e i).abelianIso.hom ≫ pullback.fst b.abelian.X.hom (U i).ι =
      y ≫ AbelianScheme.hom (e j).abelianIso.hom ≫ pullback.fst b.abelian.X.hom (U j).ι := by
  obtain ⟨m, hmi, hmj⟩ : ∃ m : Z ⟶ pullback (U i).ι (U j).ι,
      m ≫ pullback.fst (U i).ι (U j).ι = x ≫ pullback.snd a.abelian.X.hom (U i).ι ∧
      m ≫ pullback.snd (U i).ι (U j).ι = y ≫ pullback.snd a.abelian.X.hom (U j).ι :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hxy, Category.assoc,
        pullback.condition, ← Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hq : pullback.fst (U i).ι (U j).ι ≫ (U i).ι = pullback.snd (U i).ι (U j).ι ≫ (U j).ι :=
    pullback.condition
  let T : LevelBase n := levelBaseOfOpenImmersion S (pullback.snd (U i).ι (U j).ι ≫ (U j).ι)
  have hT : ∀ α : PolarizedIso (b.pullback (pullback.snd (U i).ι (U j).ι ≫ (U j).ι))
      (b.pullback (pullback.snd (U i).ι (U j).ι ≫ (U j).ι)), α = PolarizedIso.refl _ :=
    fun α => hrig T _ α
  have hxm : (x ≫ pullback.fst a.abelian.X.hom (U i).ι) ≫ a.abelian.X.hom =
      m ≫ pullback.fst (U i).ι (U j).ι ≫ (U i).ι := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hmi, Category.assoc]
  have hxm' : (x ≫ pullback.fst a.abelian.X.hom (U i).ι) ≫ a.abelian.X.hom =
      m ≫ pullback.snd (U i).ι (U j).ι ≫ (U j).ι := by
    rw [hxm, hq]
  have ex : x = pullback.lift (x ≫ pullback.fst a.abelian.X.hom (U i).ι)
      (m ≫ pullback.fst (U i).ι (U j).ι) (by rw [hxm, Category.assoc]) := by
    apply pullback.hom_ext
    · simp
    · simp [hmi]
  have ey : y = pullback.lift (x ≫ pullback.fst a.abelian.X.hom (U i).ι)
      (m ≫ pullback.snd (U i).ι (U j).ι) (by rw [hxm', Category.assoc]) := by
    apply pullback.hom_ext
    · simp [hxy]
    · simp [hmj]
  calc x ≫ AbelianScheme.hom (e i).abelianIso.hom ≫ pullback.fst b.abelian.X.hom (U i).ι
      = pullback.lift (x ≫ pullback.fst a.abelian.X.hom (U i).ι) m hxm ≫
          AbelianScheme.hom ((e i).restrict (pullback.fst (U i).ι (U j).ι)).abelianIso.hom ≫
            pullback.fst b.abelian.X.hom (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) := by
        rw [PolarizedIso.restrict_eval]
        conv_lhs => rw [ex]
    _ = pullback.lift (x ≫ pullback.fst a.abelian.X.hom (U i).ι) m hxm' ≫
          AbelianScheme.hom ((e j).restrict (pullback.snd (U i).ι (U j).ι)).abelianIso.hom ≫
            pullback.fst b.abelian.X.hom (pullback.snd (U i).ι (U j).ι ≫ (U j).ι) :=
        PolarizedIso.eval_eq_of_rigid hq hT _ _ _ _ hxm hxm'
    _ = y ≫ AbelianScheme.hom (e j).abelianIso.hom ≫ pullback.fst b.abelian.X.hom (U j).ι := by
        rw [PolarizedIso.restrict_eval]
        conv_rhs => rw [ey]

/-- The compatibility condition of the Library's étale-cover gluing of homomorphisms, for
local polarized isomorphisms under rigidity. -/
theorem compatible_of_rigid
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (hU : iSup U = ⊤)
    (a b : Datum P S.obj g d n)
    (e : ∀ i, PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι)) :
    GroupScheme.Descent.EtaleCoverHomDescent.Compatible (etaleCoverOfOpens U hU)
      (C := a.abelian.toGrp) (D := b.abelian.toGrp)
      (fun i => AbelianScheme.groupHom (e i).abelianIso.hom) :=
  fun i j x y hxy => eval_compatible_of_rigid hrig U a b e i j x y hxy

/-- Under rigidity, local polarized isomorphisms on an open cover glue to an isomorphism of
the abelian schemes. -/
def glueAbelianIso
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (hU : iSup U = ⊤)
    (a b : Datum P S.obj g d n)
    (e : ∀ i, PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι)) :
    a.abelian ≅ b.abelian :=
  ofGrpIso (GroupScheme.Descent.EtaleCoverHomDescent.iso (etaleCoverOfOpens U hU)
    (C := a.abelian.toGrp) (D := b.abelian.toGrp)
    (fun i => grpIso (e i).abelianIso) (compatible_of_rigid hrig U hU a b e)
    (compatible_of_rigid hrig U hU b a (fun i => (e i).symm)))

/-- The glued isomorphism restricts to the given local isomorphisms. -/
theorem baseChange_glueAbelianIso
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (hU : iSup U = ⊤)
    (a b : Datum P S.obj g d n)
    (e : ∀ i, PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι)) (i : I) :
    (AbelianScheme.baseChange (U i).ι).map (glueAbelianIso hrig U hU a b e).hom =
      (e i).abelianIso.hom :=
  Additive.toMul.injective (GroupScheme.Descent.EtaleCoverHomDescent.baseChange_hom
    (etaleCoverOfOpens U hU) _ (compatible_of_rigid hrig U hU a b e) i)

/-- Separation: under rigidity, two data over a level base whose restrictions to every
member of an open cover are polarized-isomorphic are polarized-isomorphic. -/
theorem Datum.isomorphic_of_isomorphic_restrict
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (hU : iSup U = ⊤)
    (a b : Datum P S.obj g d n)
    (h : ∀ i, Isomorphic (a.pullback (S.openι (U i)).hom) (b.pullback (S.openι (U i)).hom)) :
    Isomorphic a b := by
  let e : ∀ i, PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι) := fun i => (h i).some
  have hΦ := baseChange_glueAbelianIso hrig U hU a b e
  refine ⟨⟨glueAbelianIso hrig U hU a b e, ?_, ?_⟩⟩
  · apply hom_ext_of_opens U hU
    intro i
    rw [← cancel_mono
      (a.dualWitness.baseChangeIso P (U i).ι (a.dualWitness.pullback P (U i).ι)).hom]
    change (a.pullback (U i).ι).polarization = _
    rw [(e i).polarization_eq, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [DualWitness.baseChangeIso_naturality P a.dualWitness b.dualWitness (U i).ι
      (a.dualWitness.pullback P (U i).ι) (b.dualWitness.pullback P (U i).ι), hΦ i,
      ← Category.assoc ((AbelianScheme.baseChange (U i).ι).map b.polarization)]
    rfl
  · have key : mapTuple (glueAbelianIso hrig U hU a b e).hom a.level.sections =
        b.level.sections := by
      apply pullbackTuple_injective_of_opens U hU
      intro i
      rw [← pullbackTuple_map, hΦ i]
      exact funext (e i).level_eq
    intro k
    exact congrFun key k

/-- Separation for isomorphism classes: under rigidity, two classes over a level base with
equal restrictions to every member of an open cover are equal. -/
theorem Moduli.eq_of_pullback_eq
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (hU : iSup U = ⊤)
    (t t' : Moduli P S.obj g d n)
    (h : ∀ i, Moduli.pullback (S.openι (U i)).hom t = Moduli.pullback (S.openι (U i)).hom t') :
    t = t' := by
  induction t using Quotient.inductionOn with
  | h a =>
    induction t' using Quotient.inductionOn with
    | h b =>
      exact Quotient.sound (Datum.isomorphic_of_isomorphic_restrict hrig U hU a b
        (fun i => Quotient.exact (h i)))

/-- Separation for the moduli functor: under rigidity, sections over a level base with equal
restrictions to every member of an open cover are equal. -/
theorem moduliFunctor_separated
    (hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
      α = PolarizedIso.refl c)
    (hd : 0 < d) (hn : 3 ≤ n)
    {S : LevelBase n} {I : Type} (U : I → S.obj.Opens) (hU : iSup U = ⊤)
    (t t' : (moduliFunctor P g d n hd hn).obj (Opposite.op S))
    (h : ∀ i, (moduliFunctor P g d n hd hn).map (S.openι (U i)).op t =
      (moduliFunctor P g d n hd hn).map (S.openι (U i)).op t') :
    t = t' :=
  Moduli.eq_of_pullback_eq hrig U hU t t' h

end Separation

end Langlands.AbelianScheme.PolarizedFiniteLevel
