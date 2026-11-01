import Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingProof

/-! # Coherent overlap comparisons from a common module sheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Scheme.Modules.CommonSourceCocycle

open Langlands.SchemeModule.RigidifiedModule

/-- Compare an iterated pullback along three maps with a prescribed composite. -/
def normalize {W V U X : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ U) (a : U ⟶ X)
    (z : W ⟶ X) (h : t ≫ (f ≫ a) = z) (N : X.Modules) :
    (Scheme.Modules.pullback t).obj
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback a).obj N)) ⟶
      (Scheme.Modules.pullback z).obj N :=
  (Scheme.Modules.pullback t).map ((Scheme.Modules.pullbackComp f a).hom.app N) ≫
    compHom t (f ≫ a) z h N

instance normalize_isIso {W V U X : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ U)
    (a : U ⟶ X) (z : W ⟶ X) (h : t ≫ (f ≫ a) = z) (N : X.Modules) :
    IsIso (normalize t f a z h N) := by
  unfold normalize
  infer_instance

/-- Normalization can instead first compose the two innermost maps. -/
lemma normalize_eq {W V U X : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ U)
    (a : U ⟶ X) (z : W ⟶ X) (h : t ≫ (f ≫ a) = z)
    (h' : (t ≫ f) ≫ a = z) (N : X.Modules) :
    normalize t f a z h N =
      (Scheme.Modules.pullbackComp t f).hom.app ((Scheme.Modules.pullback a).obj N) ≫
        compHom (t ≫ f) a z h' N := by
  simpa only [normalize, compHom_rfl] using
    (compHom_assoc t f a (t ≫ f) (f ≫ a) z rfl rfl h' h N).symm

/-- A square comparison is compatible with any prescribed final composite. -/
lemma square_normalize {A B C D : Scheme.{u}} (p : B ⟶ D) (f : A ⟶ C)
    (g : A ⟶ B) (q : C ⟶ D) (h : f ≫ q = g ≫ p) (N : D.Modules)
    (z : A ⟶ D) (hz : g ≫ p = z) :
    (squarePullbackIso p f g q h N).hom ≫ compHom g p z hz N =
      compHom f q z (h.trans hz) N := by
  subst hz
  rw [compHom_rfl]
  simp [squarePullbackIso, compHom]

/-- Changing the last two maps of a threefold pullback preserves normalization. -/
lemma inner_square_normalize {W V A B X : Scheme.{u}}
    (t : W ⟶ V) (f : V ⟶ A) (g : V ⟶ B) (a : A ⟶ X) (b : B ⟶ X)
    (h : f ≫ a = g ≫ b) (N : X.Modules) (z : W ⟶ X)
    (ha : t ≫ (f ≫ a) = z) (hb : t ≫ (g ≫ b) = z) :
    (Scheme.Modules.pullback t).map (squarePullbackIso b f g a h N).hom ≫
        normalize t g b z hb N = normalize t f a z ha N := by
  rw [normalize_eq t g b z hb (by rw [Category.assoc, hb]),
    normalize_eq t f a z ha (by rw [Category.assoc, ha])]
  exact squarePullbackIso_comp b f g a h N t z
    (by rw [Category.assoc, hb]) (by rw [Category.assoc, ha])

/-- Changing the first two maps of a threefold pullback preserves normalization. -/
lemma outer_square_normalize {W V V' U X : Scheme.{u}}
    (t : W ⟶ V) (s : W ⟶ V') (f : V ⟶ U) (g : V' ⟶ U) (a : U ⟶ X)
    (h : t ≫ f = s ≫ g) (N : X.Modules) (z : W ⟶ X)
    (ht : t ≫ (f ≫ a) = z) (hs : s ≫ (g ≫ a) = z) :
    (squarePullbackIso g t s f h ((Scheme.Modules.pullback a).obj N)).hom ≫
        normalize s g a z hs N = normalize t f a z ht N := by
  have hz : (s ≫ g) ≫ a = z := by rw [Category.assoc, hs]
  rw [normalize_eq s g a z hs hz]
  rw [← compHom_rfl s g, ← Category.assoc,
    square_normalize g t s f h ((Scheme.Modules.pullback a).obj N) (s ≫ g) rfl]
  simpa only [normalize, compHom_rfl] using
    compHom_assoc t f a (s ≫ g) (f ≫ a) z h rfl hz ht N

/-- The canonical comparisons induced by one module satisfy the full triple-overlap
cocycle, for any commuting diagram of overlaps. -/
lemma canonical_cocycle {W Vab Vbc Vac Ua Ub Uc X : Scheme.{u}}
    (t : W ⟶ Vab) (s : W ⟶ Vbc) (r : W ⟶ Vac)
    (fab : Vab ⟶ Ua) (gab : Vab ⟶ Ub) (fbc : Vbc ⟶ Ub) (gbc : Vbc ⟶ Uc)
    (fac : Vac ⟶ Ua) (gac : Vac ⟶ Uc) (a : Ua ⟶ X) (b : Ub ⟶ X) (c : Uc ⟶ X)
    (hab : fab ≫ a = gab ≫ b) (hbc : fbc ≫ b = gbc ≫ c)
    (hac : fac ≫ a = gac ≫ c)
    (h₀ : t ≫ fab = r ≫ fac) (h₁ : t ≫ gab = s ≫ fbc)
    (h₂ : s ≫ gbc = r ≫ gac) (N : X.Modules) :
    (Scheme.Modules.pullback t).map (squarePullbackIso b fab gab a hab N).hom ≫
        (squarePullbackIso fbc t s gab h₁ ((Scheme.Modules.pullback b).obj N)).hom ≫
        (Scheme.Modules.pullback s).map (squarePullbackIso c fbc gbc b hbc N).hom ≫
        (squarePullbackIso gac s r gbc h₂ ((Scheme.Modules.pullback c).obj N)).hom =
      (squarePullbackIso fac t r fab h₀ ((Scheme.Modules.pullback a).obj N)).hom ≫
        (Scheme.Modules.pullback r).map (squarePullbackIso c fac gac a hac N).hom := by
  let z := t ≫ (fab ≫ a)
  have hta : t ≫ (fab ≫ a) = z := rfl
  have htb : t ≫ (gab ≫ b) = z := by rw [← hab]
  have hsb : s ≫ (fbc ≫ b) = z := by rw [← Category.assoc, ← h₁, Category.assoc, htb]
  have hsc : s ≫ (gbc ≫ c) = z := by rw [← hbc, hsb]
  have hra : r ≫ (fac ≫ a) = z := by rw [← Category.assoc, ← h₀, Category.assoc]
  have hrc : r ≫ (gac ≫ c) = z := by rw [← hac, hra]
  rw [← cancel_mono (normalize r gac c z hrc N)]
  simp only [Category.assoc]
  rw [outer_square_normalize s r gbc gac c h₂ N z hsc hrc,
    inner_square_normalize s fbc gbc b c hbc N z hsb hsc,
    outer_square_normalize t s gab fbc b h₁ N z htb hsb,
    inner_square_normalize t fab gab a b hab N z hta htb,
    inner_square_normalize r fac gac a c hac N z hra hrc,
    outer_square_normalize t r fab fac a h₀ N z hta hra]


/-- The overlap identification induced by identifications with pullbacks of a common module. -/
def transition {V Ua Ub X : Scheme.{u}} (f : V ⟶ Ua) (g : V ⟶ Ub)
    (a : Ua ⟶ X) (b : Ub ⟶ X) (h : f ≫ a = g ≫ b) (N : X.Modules)
    {Ma : Ua.Modules} {Mb : Ub.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ Ma)
    (eb : (Scheme.Modules.pullback b).obj N ≅ Mb) :
    (Scheme.Modules.pullback f).obj Ma ≅ (Scheme.Modules.pullback g).obj Mb :=
  (Scheme.Modules.pullback f).mapIso ea.symm ≪≫ squarePullbackIso b f g a h N ≪≫
    (Scheme.Modules.pullback g).mapIso eb

/-- Normalize a threefold pullback of a piece identified with a common module. -/
def pieceNormalize {W V U X : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ U) (a : U ⟶ X)
    (z : W ⟶ X) (h : t ≫ (f ≫ a) = z) (N : X.Modules) {M : U.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ M) :
    (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback z).obj N :=
  (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback f).map e.inv) ≫
    normalize t f a z h N

instance pieceNormalize_isIso {W V U X : Scheme.{u}} (t : W ⟶ V) (f : V ⟶ U)
    (a : U ⟶ X) (z : W ⟶ X) (h : t ≫ (f ≫ a) = z) (N : X.Modules) {M : U.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ M) :
    IsIso (pieceNormalize t f a z h N e) := by
  unfold pieceNormalize
  infer_instance

/-- Transported overlap identifications preserve normalization. -/
lemma inner_transition_normalize {W V A B X : Scheme.{u}}
    (t : W ⟶ V) (f : V ⟶ A) (g : V ⟶ B) (a : A ⟶ X) (b : B ⟶ X)
    (h : f ≫ a = g ≫ b) (N : X.Modules) {Ma : A.Modules} {Mb : B.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ Ma)
    (eb : (Scheme.Modules.pullback b).obj N ≅ Mb) (z : W ⟶ X)
    (ha : t ≫ (f ≫ a) = z) (hb : t ≫ (g ≫ b) = z) :
    (Scheme.Modules.pullback t).map (transition f g a b h N ea eb).hom ≫
        pieceNormalize t g b z hb N eb = pieceNormalize t f a z ha N ea := by
  have he : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback g).map eb.hom) ≫
      (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback g).map eb.inv) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [transition, pieceNormalize, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% he,
    inner_square_normalize t f g a b h N z ha hb]

/-- Naturality of square comparisons, kept local to the common-source construction. -/
lemma square_naturality {A B C D : Scheme.{u}} (p : B ⟶ D) (f : A ⟶ C)
    (g : A ⟶ B) (q : C ⟶ D) (h : f ≫ q = g ≫ p) {M N : D.Modules} (k : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback q).map k) ≫
        (squarePullbackIso p f g q h N).hom =
      (squarePullbackIso p f g q h M).hom ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback p).map k) :=
  (Scheme.Modules.pullbackComp f q ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp g p).symm).hom.naturality k

/-- Changing the two first maps of a piece preserves its normalized comparison. -/
lemma outer_square_pieceNormalize {W V V' U X : Scheme.{u}}
    (t : W ⟶ V) (s : W ⟶ V') (f : V ⟶ U) (g : V' ⟶ U) (a : U ⟶ X)
    (h : t ≫ f = s ≫ g) (N : X.Modules) {M : U.Modules}
    (e : (Scheme.Modules.pullback a).obj N ≅ M) (z : W ⟶ X)
    (ht : t ≫ (f ≫ a) = z) (hs : s ≫ (g ≫ a) = z) :
    (squarePullbackIso g t s f h M).hom ≫ pieceNormalize s g a z hs N e =
      pieceNormalize t f a z ht N e := by
  simp only [pieceNormalize]
  rw [← reassoc_of% (square_naturality g t s f h e.inv),
    outer_square_normalize t s f g a h N z ht hs]

/-- Overlap identifications induced by a common module satisfy the triple cocycle,
including when some of the indices coincide. -/
lemma transition_cocycle {W Vab Vbc Vac Ua Ub Uc X : Scheme.{u}}
    (t : W ⟶ Vab) (s : W ⟶ Vbc) (r : W ⟶ Vac)
    (fab : Vab ⟶ Ua) (gab : Vab ⟶ Ub) (fbc : Vbc ⟶ Ub) (gbc : Vbc ⟶ Uc)
    (fac : Vac ⟶ Ua) (gac : Vac ⟶ Uc) (a : Ua ⟶ X) (b : Ub ⟶ X) (c : Uc ⟶ X)
    (hab : fab ≫ a = gab ≫ b) (hbc : fbc ≫ b = gbc ≫ c)
    (hac : fac ≫ a = gac ≫ c)
    (h₀ : t ≫ fab = r ≫ fac) (h₁ : t ≫ gab = s ≫ fbc)
    (h₂ : s ≫ gbc = r ≫ gac) (N : X.Modules)
    {Ma : Ua.Modules} {Mb : Ub.Modules} {Mc : Uc.Modules}
    (ea : (Scheme.Modules.pullback a).obj N ≅ Ma)
    (eb : (Scheme.Modules.pullback b).obj N ≅ Mb)
    (ec : (Scheme.Modules.pullback c).obj N ≅ Mc) :
    (Scheme.Modules.pullback t).map (transition fab gab a b hab N ea eb).hom ≫
        (squarePullbackIso fbc t s gab h₁ Mb).hom ≫
        (Scheme.Modules.pullback s).map (transition fbc gbc b c hbc N eb ec).hom ≫
        (squarePullbackIso gac s r gbc h₂ Mc).hom =
      (squarePullbackIso fac t r fab h₀ Ma).hom ≫
        (Scheme.Modules.pullback r).map (transition fac gac a c hac N ea ec).hom := by
  let z := t ≫ (fab ≫ a)
  have hta : t ≫ (fab ≫ a) = z := rfl
  have htb : t ≫ (gab ≫ b) = z := by rw [← hab]
  have hsb : s ≫ (fbc ≫ b) = z := by rw [← Category.assoc, ← h₁, Category.assoc, htb]
  have hsc : s ≫ (gbc ≫ c) = z := by rw [← hbc, hsb]
  have hra : r ≫ (fac ≫ a) = z := by rw [← Category.assoc, ← h₀, Category.assoc]
  have hrc : r ≫ (gac ≫ c) = z := by rw [← hac, hra]
  rw [← cancel_mono (pieceNormalize r gac c z hrc N ec)]
  simp only [Category.assoc]
  rw [outer_square_pieceNormalize s r gbc gac c h₂ N ec z hsc hrc,
    inner_transition_normalize s fbc gbc b c hbc N eb ec z hsb hsc,
    outer_square_pieceNormalize t s gab fbc b h₁ N eb z htb hsb,
    inner_transition_normalize t fab gab a b hab N ea eb z hta htb,
    inner_transition_normalize r fac gac a c hac N ea ec z hra hrc,
    outer_square_pieceNormalize t r fab fac a h₀ N ea z hta hra]

/-- Pieces identified with pullbacks of one module give descent data on the actual
pairwise and triple scheme pullbacks of any open cover. -/
lemma openCover_cocycle {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) (N : X.Modules)
    (M : ∀ i, (𝒰.X i).Modules)
    (e : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).obj N ≅ M i) :
    OpenCoverModuleGluing.CocycleCondition 𝒰 M
      (fun i j ↦ transition (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) (𝒰.f j) pullback.condition N (e i) (e j)) := by
  intro i j k
  apply OpenCoverModuleGluing.CompEq4.of_eq
  apply transition_cocycle

end Langlands.Scheme.Modules.CommonSourceCocycle
