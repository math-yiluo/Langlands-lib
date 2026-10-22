# Actual constituent relations

Worker 47 authored these definitions for the segment and multisegment statement
branch, task `6131636b-18f8-4e15-94c2-023fb51a1970`, revision 1.

The input representations are actual complex linear actions of a group on
modules in a fixed, explicit universe. Their carriers can be infinite
dimensional. `IsIrreducibleQuotient` and `IsIrreducibleSubrepresentation`
require actual surjective and injective intertwiners, respectively, and
Mathlib's irreducibility predicate, which includes nonzeroness.

`IsIrreducibleHead` additionally says that every irreducible quotient map
has the same kernel. `IsIrreducibleSocle` says that every irreducible
embedding has the same image. Thus these definitions retain the uniqueness
of the quotient or subobject in the original statements. Merely saying
that all irreducible quotients have isomorphic targets would be weaker:
the direct sum of two copies of a simple representation has that property
without having an irreducible head. The relations do not assert that heads
or socles exist, select a representative, or carry a classification theorem
as a structure field.

The target and all representations tested for uniqueness have carriers in
the same universe as the source. No smallness or cross-universe quotient
theorem is implicit. Later classification statements must quantify their
actual induction representation in a universe containing its function
space. Their equivalence conclusions use actual linear representation
isomorphisms.

`HasScalarCharacter` is the explicit scalar-action formula along a supplied
group homomorphism. Specializing this homomorphism to scalar matrices gives
the prescribed central character of a positive-rank general linear group.
This definition does not require a chosen central character to exist.

The relations are algebraic and therefore have a broader domain than the
smooth representations in the originals. Their use for smooth representations
does not add continuity or a topology on the representation carrier.
They describe possible constituents; they do not construct normalized
parabolic induction, segments, or canonical special/Langlands quotients.
Worker 23 retains those construction responsibilities.

## Source correspondence

| Declarations | Original passage and translation |
| --- | --- |
| `IsIrreducibleQuotient`, `IsIrreducibleSubrepresentation` | Bernstein–Zelevinsky 1977 §1.2, p.443, PDF p.4: actual complex smooth modules, equivalence and subquotients. The formal relations use intertwiners with surjective/injective underlying linear maps. |
| `IsIrreducibleHead`, `IsIrreducibleSocle` | Zelevinsky 1980 §3.1, pp.180–181, PDF pp.17–18; §6.1, p.188, PDF p.25; §9.1, p.197, PDF p.34. The earlier segment constituent is the submodule of increasing induction; the special constituent is its quotient. The formal uniqueness condition is equality of actual kernels/images, not an assumed canonical constructor. |
| `HasScalarCharacter` | Internal explicit predicate for scalar action. Bernstein–Zelevinsky 1977 §1.5, p.443 defines scalar twisting; §4.2, p.454, PDF p.15 uses the central character to distinguish adjacent norm twists. No central-character existence theorem is attributed to these passages. |

The original passages were read directly. Registered source fingerprints:

- `bernstein-zelevinsky-1977-induced-i`:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- `zelevinsky-1980-induced-ii`:
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.

The retained files are the Bernstein–Zelevinsky 1977 and Zelevinsky 1980
original PDFs linked in `literature/_central-library-pointers.md`.
These predicate definitions have no project mathematical imports.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
All constructions inside the predicates come from Mathlib's actual
representations, intertwiners, kernels, images, and irreducibility.

This file contains definitions only. Development compilation, independent
acceptance and publication are distinct statuses; no classification theorem
or constituent-existence theorem is proved here.
