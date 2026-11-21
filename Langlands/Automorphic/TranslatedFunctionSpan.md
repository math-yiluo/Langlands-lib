# Operator actions on spans of translated functions

Start with a linear map from a coefficient space to functions and a monoid representation on those functions. `translatedFunctionSum` evaluates a finite family of coefficients by translating and summing their functions. `TranslatedFunctionSpan` is the quotient of the family space by zero evaluation. Its evaluation map into functions is injective.

The monoid translates the represented functions by shifting the family indices. An algebra acting on the coefficient space acts on the quotient whenever the zero-evaluation kernel is stable under its coefficientwise action. These two actions commute because shifting indices commutes with acting on coefficients. If every original function has finite-dimensional translate span, then so does every quotient element, by taking a finite sum of translate orbits.

This is an internal construction for the constant-term representation in Task 6823. In the application, the acting monoid is the block idele centre, the coefficient algebra is the full automorphic operator algebra, and the kernel condition follows from differentiating and translating the actual constant term.
