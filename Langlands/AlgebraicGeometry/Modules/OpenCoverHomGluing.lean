import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluingStatement
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs

/-! # Gluing actual module morphisms over a scheme open cover -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules.OpenCoverHomGluing

section Glue

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type*} {V : ι → X.Opens}

/-- The underlying sheaf of abelian groups of a module. -/
abbrev sheafAb (N : X.Modules) : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩

lemma le_iSup_inf (hV : ∀ x : X, ∃ i, x ∈ V i) (O : X.Opens) : O ≤ ⨆ k, O ⊓ V k := by
  intro x hx
  obtain ⟨k, hk⟩ := hV x
  exact Opens.mem_iSup.mpr ⟨k, ⟨hx, hk⟩⟩

lemma map_map_eq {F : X.Modules} {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (h₃ : C ≤ A)
    (x : Γ(F, A)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op x) =
      F.presheaf.map (homOfLE h₃).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma map_le_refl {F : X.Modules} {A : X.Opens} (x : Γ(F, A)) :
    F.presheaf.map (homOfLE (le_refl A)).op x = x := by
  rw [show (homOfLE (le_refl A)).op = 𝟙 (op A) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- Sections of a module agreeing on the members of a cover agree. -/
lemma eq_of_local (hV : ∀ x : X, ∃ i, x ∈ V i) {N : X.Modules} {O : X.Opens}
    (s t : Γ(N, O))
    (h : ∀ k, N.presheaf.map (homOfLE (inf_le_left : O ⊓ V k ≤ O)).op s =
      N.presheaf.map (homOfLE (inf_le_left : O ⊓ V k ≤ O)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (sheafAb N) (fun k => O ⊓ V k) O (fun _ => homOfLE inf_le_left)
    (le_iSup_inf hV O) s t h

/-- Restriction commutes with a morphism of modules, on sections. -/
lemma hom_map_app {M N : X.Modules} (f : M ⟶ N) {P Q : X.Opens} (h : Q ≤ P) (x : Γ(M, P)) :
    N.presheaf.map (homOfLE h).op (f.app P x) = f.app Q (M.presheaf.map (homOfLE h).op x) :=
  (ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE h).op) x).symm

variable (V) in
/-- Linear maps on the sections over all opens inside members of a family of opens,
compatible with restriction and with each other. -/
structure LocalFamily (M N : X.Modules) where
  /-- The map on sections over an open `P` contained in `V i`. -/
  θ : ∀ i (P : X.Opens), P ≤ V i → (Γ(M, P) ⟶ Γ(N, P))
  nat : ∀ i (P Q : X.Opens) (hP : P ≤ V i) (hQP : Q ≤ P) (x : Γ(M, P)),
    N.presheaf.map (homOfLE hQP).op (θ i P hP x) =
      θ i Q (hQP.trans hP) (M.presheaf.map (homOfLE hQP).op x)
  smul : ∀ i (P : X.Opens) (hP : P ≤ V i) (r : Γ(X, P)) (x : Γ(M, P)),
    θ i P hP (r • x) = r • θ i P hP x
  compat : ∀ i j (P : X.Opens) (hi : P ≤ V i) (hj : P ≤ V j), θ i P hi = θ j P hj

namespace LocalFamily

variable {M N : X.Modules} (D : LocalFamily V M N) (hV : ∀ x : X, ∃ i, x ∈ V i)

include hV in
lemma exists_glue (O : X.Opens) (x : Γ(M, O)) :
    ∃ s : Γ(N, O), ∀ k, N.presheaf.map (homOfLE (inf_le_left : O ⊓ V k ≤ O)).op s =
      D.θ k (O ⊓ V k) inf_le_right (M.presheaf.map (homOfLE (inf_le_left : O ⊓ V k ≤ O)).op x) := by
  refine (TopCat.Sheaf.existsUnique_gluing' (sheafAb N)
    (fun k => O ⊓ V k) O (fun k => homOfLE inf_le_left) (le_iSup_inf hV O)
    (fun k => D.θ k (O ⊓ V k) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op x)) ?_).exists
  intro k l
  change N.presheaf.map (homOfLE inf_le_left).op _ = N.presheaf.map (homOfLE inf_le_right).op _
  rw [D.nat, D.nat, D.compat k l, map_map_eq _ _ (inf_le_left.trans inf_le_left),
    map_map_eq _ _ (inf_le_left.trans inf_le_left)]

/-- The glued section. -/
def glue (O : X.Opens) (x : Γ(M, O)) : Γ(N, O) := (D.exists_glue hV O x).choose

lemma glue_spec₀ (O : X.Opens) (x : Γ(M, O)) (k : ι) :
    N.presheaf.map (homOfLE (inf_le_left : O ⊓ V k ≤ O)).op (D.glue hV O x) =
      D.θ k (O ⊓ V k) inf_le_right (M.presheaf.map (homOfLE (inf_le_left : O ⊓ V k ≤ O)).op x) :=
  (D.exists_glue hV O x).choose_spec k

lemma glue_spec {O Q : X.Opens} (hQO : Q ≤ O) (i : ι) (hQ : Q ≤ V i) (x : Γ(M, O)) :
    N.presheaf.map (homOfLE hQO).op (D.glue hV O x) =
      D.θ i Q hQ (M.presheaf.map (homOfLE hQO).op x) := by
  apply eq_of_local hV
  intro k
  rw [map_map_eq _ _ (inf_le_left.trans hQO),
    ← map_map_eq (inf_le_left : O ⊓ V k ≤ O) (inf_le_inf_right (V k) hQO),
    D.glue_spec₀, D.nat, D.nat, D.compat i k, map_map_eq _ _ (inf_le_left.trans hQO),
    map_map_eq _ _ (inf_le_left.trans hQO)]

lemma glue_add (O : X.Opens) (x y : Γ(M, O)) :
    D.glue hV O (x + y) = D.glue hV O x + D.glue hV O y := by
  apply eq_of_local hV
  intro k
  rw [map_add, D.glue_spec₀, D.glue_spec₀, D.glue_spec₀, map_add, map_add]

lemma glue_smul (O : X.Opens) (r : Γ(X, O)) (x : Γ(M, O)) :
    D.glue hV O (r • x) = r • D.glue hV O x := by
  apply eq_of_local hV
  intro k
  rw [Scheme.Modules.map_smul, D.glue_spec₀, D.glue_spec₀, Scheme.Modules.map_smul, D.smul]

lemma glue_map {O O' : X.Opens} (h : O' ≤ O) (x : Γ(M, O)) :
    D.glue hV O' (M.presheaf.map (homOfLE h).op x) =
      N.presheaf.map (homOfLE h).op (D.glue hV O x) := by
  apply eq_of_local hV
  intro k
  rw [map_map_eq _ _ (inf_le_left.trans h), D.glue_spec₀, D.glue_spec hV _ k inf_le_right,
    map_map_eq]

/-- The glued morphism of abelian presheaves. -/
def presheafHom : M.presheaf ⟶ N.presheaf where
  app O := AddCommGrpCat.ofHom (AddMonoidHom.mk' (D.glue hV O.unop) (D.glue_add hV O.unop))
  naturality O O' g := by
    ext x
    exact D.glue_map hV (leOfHom g.unop) x

/-- The glued morphism of modules. -/
def hom : M ⟶ N :=
  ⟨PresheafOfModules.homMk (D.presheafHom hV) fun O r x => D.glue_smul hV O.unop r x⟩

lemma hom_app_apply (O : X.Opens) (x : Γ(M, O)) : (D.hom hV).app O x = D.glue hV O x := rfl

lemma hom_app (i : ι) (P : X.Opens) (hP : P ≤ V i) : (D.hom hV).app P = D.θ i P hP := by
  ext x
  rw [hom_app_apply, ← map_le_refl (D.glue hV P x), D.glue_spec hV (le_refl P) i hP, map_le_refl]

end LocalFamily

/-- Morphisms of modules agreeing on all opens inside members of a cover agree. -/
lemma hom_ext_of_local (hV : ∀ x : X, ∃ i, x ∈ V i) {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i (P : X.Opens), P ≤ V i → f.app P = g.app P) : f = g := by
  ext O x
  apply eq_of_local hV
  intro k
  rw [hom_map_app, hom_map_app, h k _ inf_le_right]

end Glue

section Transport

variable {X U : AlgebraicGeometry.Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] {M N : X.Modules}

lemma le_image_preimage {P : X.Opens} (hP : P ≤ f.opensRange) : P ≤ f ''ᵁ f ⁻¹ᵁ P := by
  rw [f.image_preimage_eq_opensRange_inf]
  exact le_inf hP le_rfl

/-- The map on sections over an open inside the range of `f` induced by a morphism of
restrictions along `f`. -/
def transport (ψ : M.restrict f ⟶ N.restrict f) (P : X.Opens) (hP : P ≤ f.opensRange) :
    Γ(M, P) ⟶ Γ(N, P) :=
  M.presheaf.map (homOfLE (f.image_preimage_le P)).op ≫ (M.restrictAppIso f _).inv ≫
    ψ.app (f ⁻¹ᵁ P) ≫ (N.restrictAppIso f _).hom ≫
    N.presheaf.map (homOfLE (le_image_preimage f hP)).op

lemma transport_eq (ψ : M.restrict f ⟶ N.restrict f) (P : X.Opens) (hP : P ≤ f.opensRange)
    (A : U.Opens) (p : op P ⟶ op (f ''ᵁ A)) (q : op (f ''ᵁ A) ⟶ op P) :
    transport f ψ P hP = M.presheaf.map p ≫ (M.restrictAppIso f A).inv ≫ ψ.app A ≫
      (N.restrictAppIso f A).hom ≫ N.presheaf.map q := by
  have hPA : P = f ''ᵁ A := le_antisymm (leOfHom q.unop) (leOfHom p.unop)
  obtain rfl : f ⁻¹ᵁ P = A := by rw [hPA, f.preimage_image_eq]
  rfl

/-- Naturality of a morphism of restrictions, read on the sections of the original modules. -/
lemma restrict_hom_map (ψ : M.restrict f ⟶ N.restrict f) {A B : U.Opens} (h : B ≤ A)
    (y : Γ(M, f ''ᵁ A)) :
    N.presheaf.map (homOfLE (f.image_mono h)).op
        ((N.restrictAppIso f A).hom (ψ.app A ((M.restrictAppIso f A).inv y))) =
      (N.restrictAppIso f B).hom (ψ.app B ((M.restrictAppIso f B).inv
        (M.presheaf.map (homOfLE (f.image_mono h)).op y))) :=
  hom_map_app ψ h _

lemma restrictAppIso_inv_smul (F : X.Modules) (A : U.Opens) (s : Γ(X, f ''ᵁ A))
    (y : Γ(F, f ''ᵁ A)) :
    (F.restrictAppIso f A).inv (s • y) = (f.appIso A).hom s • (F.restrictAppIso f A).inv y := by
  change s • y = (f.appIso A).inv ((f.appIso A).hom s) • y
  rw [Iso.hom_inv_id_apply]

lemma restrictAppIso_hom_smul (F : X.Modules) (A : U.Opens) (r : Γ(U, A))
    (y : Γ(F.restrict f, A)) :
    (F.restrictAppIso f A).hom (r • y) = (f.appIso A).inv r • (F.restrictAppIso f A).hom y :=
  rfl

lemma restrict_hom_smul (ψ : M.restrict f ⟶ N.restrict f) (A : U.Opens) (s : Γ(X, f ''ᵁ A))
    (y : Γ(M, f ''ᵁ A)) :
    (N.restrictAppIso f A).hom (ψ.app A ((M.restrictAppIso f A).inv (s • y))) =
      s • (N.restrictAppIso f A).hom (ψ.app A ((M.restrictAppIso f A).inv y)) := by
  rw [restrictAppIso_inv_smul, Scheme.Modules.Hom.app_smul, restrictAppIso_hom_smul,
    Iso.hom_inv_id_apply]

lemma scalar_map_map {A B : X.Opens} (h₁ : B ≤ A) (h₂ : A ≤ B) (r : Γ(X, A)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op r) = r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    show (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 (op A) from rfl, CategoryTheory.Functor.map_id]
  rfl

lemma transport_map (ψ : M.restrict f ⟶ N.restrict f) (P Q : X.Opens) (hP : P ≤ f.opensRange)
    (hQP : Q ≤ P) (x : Γ(M, P)) :
    N.presheaf.map (homOfLE hQP).op (transport f ψ P hP x) =
      transport f ψ Q (hQP.trans hP) (M.presheaf.map (homOfLE hQP).op x) := by
  simp only [transport, ConcreteCategory.comp_apply]
  rw [map_map_eq _ _ (hQP.trans (le_image_preimage f hP)),
    map_map_eq _ _ ((f.image_preimage_le Q).trans hQP),
    ← map_map_eq (f.image_preimage_le P) (f.image_mono (f.preimage_mono hQP)) _,
    ← restrict_hom_map f ψ (f.preimage_mono hQP), map_map_eq]

lemma transport_smul (ψ : M.restrict f ⟶ N.restrict f) (P : X.Opens) (hP : P ≤ f.opensRange)
    (r : Γ(X, P)) (x : Γ(M, P)) :
    transport f ψ P hP (r • x) = r • transport f ψ P hP x := by
  simp only [transport, ConcreteCategory.comp_apply]
  rw [Scheme.Modules.map_smul, restrict_hom_smul, Scheme.Modules.map_smul, scalar_map_map]

end Transport

section Overlap

open AlgebraicGeometry.Scheme.Modules (pullbackComp pullbackCongr restrictFunctor
  restrictFunctorIsoPullback)
open Langlands.SchemeModule.RigidifiedModule (compHom)

variable {A B C : AlgebraicGeometry.Scheme.{u}}

/-- Conjugating a pulled-back morphism by the composition comparison agrees with iterated
restriction. -/
lemma conj_eq (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] {M N : C.Modules}
    (φ : (Scheme.Modules.pullback b).obj M ⟶ (Scheme.Modules.pullback b).obj N) :
    (restrictFunctorIsoPullback c).hom.app M ≫ inv (compHom a b c h M) ≫ (Scheme.Modules.pullback a).map φ ≫
        compHom a b c h N ≫ (restrictFunctorIsoPullback c).inv.app N =
      (restrictCompIso a b c h).hom.app M ≫
        (restrictFunctor a).map ((restrictFunctorIsoPullback b).hom.app M ≫ φ ≫
          (restrictFunctorIsoPullback b).inv.app N) ≫ (restrictCompIso a b c h).inv.app N := by
  rw [← cancel_mono ((restrictFunctorIsoPullback c).hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← restrictCompIso_hom_app_comp a b c h M, ← restrictCompIso_hom_app_comp a b c h N]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc (restrictFunctor a) ((restrictFunctorIsoPullback b).inv.app N),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    (restrictFunctorIsoPullback a).hom.naturality_assoc φ]

/-- The square comparison followed by the composition comparison for the second composite is the
composition comparison for the first composite. -/
lemma squarePullbackIso_hom_compHom {X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y) (hs : p' ≫ t = s ≫ p) (M : Y.Modules) :
    (squarePullbackIso p p' s t hs M).hom ≫ compHom s p (p' ≫ t) hs.symm M =
      compHom p' t (p' ≫ t) rfl M := by
  simp [squarePullbackIso, compHom, pullbackCongr]

/-- The overlap condition of the statement, rewritten with composition comparisons. -/
lemma conj_square {X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y) (hs : p' ≫ t = s ≫ p) {M N : Y.Modules}
    (φt : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj N)
    (φp : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback p).obj N)
    (H : (Scheme.Modules.pullback p').map φt ≫ (squarePullbackIso p p' s t hs N).hom =
      (squarePullbackIso p p' s t hs M).hom ≫ (Scheme.Modules.pullback s).map φp) :
    inv (compHom p' t (p' ≫ t) rfl M) ≫ (Scheme.Modules.pullback p').map φt ≫
        compHom p' t (p' ≫ t) rfl N =
      inv (compHom s p (p' ≫ t) hs.symm M) ≫ (Scheme.Modules.pullback s).map φp ≫
        compHom s p (p' ≫ t) hs.symm N := by
  rw [← cancel_epi (compHom p' t (p' ≫ t) rfl M), IsIso.hom_inv_id_assoc,
    ← squarePullbackIso_hom_compHom p p' s t hs M, ← squarePullbackIso_hom_compHom p p' s t hs N,
    reassoc_of% H]
  simp

variable {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}

/-- The morphism of restrictions corresponding to a morphism of pullbacks along an open
immersion. -/
def restrictHom {U : AlgebraicGeometry.Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    M.restrict f ⟶ N.restrict f :=
  (restrictFunctorIsoPullback f).hom.app M ≫ φ ≫ (restrictFunctorIsoPullback f).inv.app N

lemma transport_restrictHom_eq {U : AlgebraicGeometry.Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (P : X.Opens) (hP : P ≤ f.opensRange) (A : U.Opens) (p : op P ⟶ op (f ''ᵁ A))
    (q : op (f ''ᵁ A) ⟶ op P) :
    transport f (restrictHom f φ) P hP = M.presheaf.map p ≫
      Scheme.Modules.Hom.app ((restrictFunctorIsoPullback f).hom.app M) A ≫
        Scheme.Modules.Hom.app φ A ≫
          Scheme.Modules.Hom.app ((restrictFunctorIsoPullback f).inv.app N) A ≫
            N.presheaf.map q := by
  rw [transport_eq f _ P hP A p q]
  rfl

/-- Local maps that agree after conjugated pullback to an overlap induce the same maps on the
sections over opens of `X` inside the overlap. -/
lemma transport_compat {Ui Uj Z : AlgebraicGeometry.Scheme.{u}} (ui : Ui ⟶ X) (uj : Uj ⟶ X)
    (p' : Z ⟶ Ui) (s : Z ⟶ Uj) [IsOpenImmersion ui] [IsOpenImmersion uj] [IsOpenImmersion p']
    [IsOpenImmersion s] (hs : p' ≫ ui = s ≫ uj)
    (hrange : ui.opensRange ⊓ uj.opensRange ≤ (p' ≫ ui).opensRange)
    (φi : (Scheme.Modules.pullback ui).obj M ⟶ (Scheme.Modules.pullback ui).obj N)
    (φj : (Scheme.Modules.pullback uj).obj M ⟶ (Scheme.Modules.pullback uj).obj N)
    (H : inv (compHom p' ui (p' ≫ ui) rfl M) ≫ (Scheme.Modules.pullback p').map φi ≫
        compHom p' ui (p' ≫ ui) rfl N =
      inv (compHom s uj (p' ≫ ui) hs.symm M) ≫ (Scheme.Modules.pullback s).map φj ≫
        compHom s uj (p' ≫ ui) hs.symm N)
    (P : X.Opens) (hi : P ≤ ui.opensRange) (hj : P ≤ uj.opensRange) :
    transport ui (restrictHom ui φi) P hi = transport uj (restrictHom uj φj) P hj := by
  have key := conj_eq p' ui (p' ≫ ui) rfl φi
  rw [reassoc_of% H, conj_eq s uj (p' ≫ ui) hs.symm φj] at key
  have hP : P ≤ (p' ≫ ui).opensRange := (le_inf hi hj).trans hrange
  obtain ⟨W, rfl⟩ : ∃ W, P = (p' ≫ ui) ''ᵁ W :=
    ⟨(p' ≫ ui) ⁻¹ᵁ P, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hP]⟩
  have k := congrArg (fun g => Scheme.Modules.Hom.app g W) key
  simp only [Scheme.Modules.Hom.comp_app, restrictCompIso, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, restrictFunctor_map_app, Category.assoc] at k
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp] at k
  exact (transport_restrictHom_eq ui φi _ hi (p' ''ᵁ W) _ _).trans
    (k.symm.trans (transport_restrictHom_eq uj φj _ hj (s ''ᵁ W) _ _).symm)

end Overlap

section Main

open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorIsoPullback)

variable {X U : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (f : U ⟶ X) [IsOpenImmersion f]

lemma restrictHom_pullback_map (g : M ⟶ N) :
    restrictHom f ((Scheme.Modules.pullback f).map g) = (restrictFunctor f).map g := by
  rw [restrictHom, ← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]

lemma pullback_map_eq_of_app (g : M ⟶ N)
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (h : ∀ W : U.Opens, g.app (f ''ᵁ W) = (restrictHom f φ).app W) :
    (Scheme.Modules.pullback f).map g = φ := by
  have e : restrictHom f ((Scheme.Modules.pullback f).map g) = restrictHom f φ := by
    rw [restrictHom_pullback_map]
    ext W : 1
    exact h W
  exact (cancel_mono ((restrictFunctorIsoPullback f).inv.app N)).1
    ((cancel_epi ((restrictFunctorIsoPullback f).hom.app M)).1 e)

lemma app_image_eq_of_pullback_map (g : M ⟶ N)
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (h : (Scheme.Modules.pullback f).map g = φ) (W : U.Opens) :
    g.app (f ''ᵁ W) = (restrictHom f φ).app W := by
  subst h
  rw [restrictHom_pullback_map]
  rfl

lemma transport_image (ψ : M.restrict f ⟶ N.restrict f) (W : U.Opens)
    (h : f ''ᵁ W ≤ f.opensRange) : transport f ψ (f ''ᵁ W) h = ψ.app W := by
  rw [transport_eq f ψ _ h W (𝟙 _) (𝟙 _), CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

end Main

/-- Compatible morphisms between the pullbacks of two modules along the members of an open cover
glue to a unique morphism of modules. -/
theorem openCoverHomGluing : OpenCoverHomGluingStatement.{u} := by
  intro X 𝒰 M N φ hφ
  have hV : ∀ x : X, ∃ i, x ∈ (𝒰.f i).opensRange := fun x => ⟨𝒰.idx x, 𝒰.covers x⟩
  let D : LocalFamily (fun i => (𝒰.f i).opensRange) M N :=
    { θ := fun i P hP => transport (𝒰.f i) (restrictHom (𝒰.f i) (φ i)) P hP
      nat := fun i P Q hP hQP x => transport_map _ _ P Q hP hQP x
      smul := fun i P hP r x => transport_smul _ _ P hP r x
      compat := fun i j P hi hj =>
        transport_compat (𝒰.f i) (𝒰.f j) (pullback.fst _ _) (pullback.snd _ _)
          pullback.condition
          (Opens.ext (IsOpenImmersion.range_pullback_to_base_of_left (𝒰.f i) (𝒰.f j))).ge
          (φ i) (φ j)
          (conj_square _ _ _ _ _ _ _ (hφ i j)) P hi hj }
  have key : ∀ i (W : (𝒰.X i).Opens),
      (D.hom hV).app ((𝒰.f i) ''ᵁ W) = (restrictHom (𝒰.f i) (φ i)).app W := fun i W => by
    rw [D.hom_app hV i _ ((𝒰.f i).image_le_opensRange W)]
    exact transport_image _ _ W ((𝒰.f i).image_le_opensRange W)
  refine ⟨D.hom hV, fun i => pullback_map_eq_of_app _ _ _ (key i), ?_⟩
  intro g hg
  apply hom_ext_of_local hV
  intro i P hP
  obtain ⟨W, rfl⟩ : ∃ W, P = (𝒰.f i) ''ᵁ W :=
    ⟨(𝒰.f i) ⁻¹ᵁ P, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hP]⟩
  rw [key, app_image_eq_of_pullback_map _ g _ (hg i)]

end Langlands.Scheme.Modules.OpenCoverHomGluing
